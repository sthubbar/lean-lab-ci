/-
P0069, pages 22 and 23, the spacing estimates and principal residue
sum in Lemma 9. These are elementary bounds for the finite kernel sum.
AI wrote the Lean code. CODEX task132, 2026-10-26. Goldbach is open.
-/
import LeanLab.BHP1997.MeanValue132

namespace LeanLab.BHP1997.Spacing132
open Classical Real Finset

/-- Pages 22 and 23, spacing detail: For a at least 1, one divided by a to the fourth is at most twice the difference between one divided by a and one divided by a plus 1. -/
theorem reciprocal_fourth_step {a : ℝ} (ha : 1 ≤ a) :
    1 / a ^ 4 ≤ 2 * (1 / a - 1 / (a + 1)) := by
  have ha0 : 0 < a := by linarith
  have heq : 2 * (1 / a - 1 / (a + 1)) = 2 / (a * (a + 1)) := by
    field_simp
    ring
  rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
  have hs : 1 ≤ a ^ 2 := by nlinarith
  have hfour := mul_nonneg (sq_nonneg a) (show 0 ≤ a ^ 2 - 1 by linarith)
  nlinarith

/-- Pages 22 and 23, spacing detail: The sum of reciprocal fourth powers from 1 through M is at most twice one minus one divided by M plus 1. -/
theorem reciprocal_fourth_sum (M : ℕ) :
    ∑ k ∈ Finset.range M, 1 / (1 + (k : ℝ)) ^ 4 ≤ 2 * (1 - 1 / (M + 1 : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hstep := reciprocal_fourth_step (a := 1 + (M : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) M; linarith)
    have heq : 2 * (1 - 1 / (M + 1 : ℝ)) +
        2 * (1 / (1 + (M : ℝ)) - 1 / (1 + (M : ℝ) + 1)) =
          2 * (1 - 1 / ((M + 1 : ℕ) + 1 : ℝ)) := by push_cast; ring
    linarith

/-- Pages 22 and 23, spacing detail: For a finite set of nonnegative real points separated by at least 1, the sum of one divided by one plus t to the fourth is at most 2. -/
theorem nonnegative_spaced_tail (S : Finset ℝ)
    (hnonneg : ∀ t ∈ S, 0 ≤ t)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|) :
    ∑ t ∈ S, 1 / (1 + t) ^ 4 ≤ 2 := by
  let f : ℝ → ℕ := fun t => ⌊t⌋₊
  have hinj : Set.InjOn f S := by
    intro t ht u hu htu
    by_contra hne
    have h1 := Nat.floor_le (hnonneg t ht)
    have h2 := Nat.lt_floor_add_one t
    have h3 := Nat.floor_le (hnonneg u hu)
    have h4 := Nat.lt_floor_add_one u
    have heq : ⌊t⌋₊ = ⌊u⌋₊ := htu
    rw [heq] at h1 h2
    have habs : |t - u| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith [hspace t ht u hu hne]
  let M := (∑ t ∈ S, f t) + 1
  have hsub : S.image f ⊆ Finset.range M := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have hle : f t ≤ ∑ u ∈ S, f u := Finset.single_le_sum (fun u _ => Nat.zero_le (f u)) ht
    omega
  have himage : (∑ k ∈ S.image f, 1 / (1 + (k : ℝ)) ^ 4) =
      ∑ t ∈ S, 1 / (1 + (f t : ℝ)) ^ 4 := Finset.sum_image hinj
  calc
    (∑ t ∈ S, 1 / (1 + t) ^ 4) ≤ ∑ t ∈ S, 1 / (1 + (f t : ℝ)) ^ 4 := by
      apply Finset.sum_le_sum
      intro t ht
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
      exact Nat.floor_le (hnonneg t ht)
    _ = ∑ k ∈ S.image f, 1 / (1 + (k : ℝ)) ^ 4 := himage.symm
    _ ≤ ∑ k ∈ Finset.range M, 1 / (1 + (k : ℝ)) ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ 2 * (1 - 1 / (M + 1 : ℝ)) := reciprocal_fourth_sum M
    _ ≤ 2 := by
      have hpos : (0 : ℝ) ≤ 1 / (M + 1 : ℝ) := by positivity
      linarith

/-- Pages 22 and 23, spacing detail: For a finite set of real points separated by at least 1, the sum of one divided by one plus absolute t to the fourth is at most 4. -/
theorem spaced_tail (S : Finset ℝ)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|) :
    ∑ t ∈ S, 1 / (1 + |t|) ^ 4 ≤ 4 := by
  let P := S.filter (fun t => 0 ≤ t)
  let M := S.filter (fun t => t < 0)
  let Q := M.image (fun t => -t)
  have hpos : (∑ t ∈ P, 1 / (1 + |t|) ^ 4) ≤ 2 := by
    have hh := nonnegative_spaced_tail P
      (fun t ht => (Finset.mem_filter.mp ht).2)
      (fun t ht u hu hne => hspace t (Finset.mem_filter.mp ht).1
        u (Finset.mem_filter.mp hu).1 hne)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [abs_of_nonneg (Finset.mem_filter.mp ht).2]
  have hQnonneg : ∀ t ∈ Q, 0 ≤ t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    have := (Finset.mem_filter.mp hu).2
    linarith
  have hQspace : ∀ t ∈ Q, ∀ u ∈ Q, t ≠ u → 1 ≤ |t - u| := by
    intro t ht u hu hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    have hab : a ≠ b := by intro heq; exact hne (by rw [heq])
    have hh := hspace a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hneg : (∑ t ∈ M, 1 / (1 + |t|) ^ 4) ≤ 2 := by
    have hh := nonnegative_spaced_tail Q hQnonneg hQspace
    have heq : (∑ t ∈ Q, 1 / (1 + t) ^ 4) = ∑ t ∈ M, 1 / (1 + |t|) ^ 4 := by
      rw [show Q = M.image (fun t => -t) from rfl, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro t ht
        rw [abs_of_neg (Finset.mem_filter.mp ht).2]
      · intro a ha b hb heq
        exact neg_injective heq
    rw [heq] at hh
    exact hh
  have hsplit : (∑ t ∈ S, 1 / (1 + |t|) ^ 4) =
      (∑ t ∈ P, 1 / (1 + |t|) ^ 4) + (∑ t ∈ M, 1 / (1 + |t|) ^ 4) := by
    simpa only [P, M, not_le] using
      (Finset.sum_filter_add_sum_filter_not S (fun t => 0 ≤ t) (fun t => 1 / (1 + |t|) ^ 4)).symm
  linarith

/-- Pages 22 and 23, spacing detail: For a well-spaced set of time and character pairs, the principal-character residue sum in Lemma 9 is at most 4. -/
theorem principal_tail_le {q : ℕ} (S : Finset (ℝ × DirichletCharacter ℂ q))
    (hspace : LeanLab.BHP1997.Thm4.WellSpaced S) :
    (∑ p ∈ S, if p.2 = 1 then 1 / (1 + |p.1|) ^ 4 else 0) ≤ 4 := by
  let P := S.filter (fun p => p.2 = 1)
  let X := P.image Prod.fst
  have hinj : Set.InjOn Prod.fst (P : Set (ℝ × DirichletCharacter ℂ q)) := by
    intro p hp r hr heq
    apply Prod.ext heq
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm
  have hXspace : ∀ t ∈ X, ∀ u ∈ X, t ≠ u → 1 ≤ |t - u| := by
    intro t ht u hu hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    apply hspace p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1
    · intro heq
      exact hne (congrArg Prod.fst heq)
    · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm
  have hh := spaced_tail X hXspace
  have heq : (∑ p ∈ S, if p.2 = 1 then 1 / (1 + |p.1|) ^ 4 else 0) =
      ∑ t ∈ X, 1 / (1 + |t|) ^ 4 := by
    rw [show X = P.image Prod.fst from rfl, Finset.sum_image hinj]
    exact (Finset.sum_filter ..).symm
  rw [heq]
  exact hh

/-- Page 22, the principal-character residue in Lemma 9 contributes
at most 4 times N squared. This uses spacing only. -/
theorem remainder_le {q : ℕ} (x N T : ℝ)
    (S : Finset (ℝ × DirichletCharacter ℂ q)) (hspace : Thm4.WellSpaced S) :
    MeanValue132.remainder x N T S ≤
      Real.log x ^ 4 * (S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) + 4 * N ^ 2 := by
  unfold MeanValue132.remainder
  have ht := principal_tail_le S hspace
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg N)]

/-- Pages 22 and 23, spacing detail: For nonnegative points separated by at least 1 and lying below a natural M, the reciprocal first-power sum is at most 1 plus log M. -/
theorem nonnegative_spaced_harmonic (S : Finset ℝ) (M : ℕ)
    (hnonneg : ∀ t ∈ S, 0 ≤ t)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|)
    (hbound : ∀ t ∈ S, t < (M : ℝ)) :
    ∑ t ∈ S, 1 / (1 + t) ≤ 1 + Real.log M := by
  let f : ℝ → ℕ := fun t => ⌊t⌋₊
  have hinj : Set.InjOn f S := by
    intro t ht u hu htu
    by_contra hne
    have h1 := Nat.floor_le (hnonneg t ht)
    have h2 := Nat.lt_floor_add_one t
    have h3 := Nat.floor_le (hnonneg u hu)
    have h4 := Nat.lt_floor_add_one u
    have heq : ⌊t⌋₊ = ⌊u⌋₊ := htu
    rw [heq] at h1 h2
    have habs : |t - u| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith [hspace t ht u hu hne]
  have hsub : S.image f ⊆ Finset.range M := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have hlt : (⌊t⌋₊ : ℝ) < M := lt_of_le_of_lt (Nat.floor_le (hnonneg t ht)) (hbound t ht)
    exact_mod_cast hlt
  have himage : (∑ k ∈ S.image f, 1 / (1 + (k : ℝ))) =
      ∑ t ∈ S, 1 / (1 + (f t : ℝ)) := Finset.sum_image hinj
  calc
    (∑ t ∈ S, 1 / (1 + t)) ≤ ∑ t ∈ S, 1 / (1 + (f t : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      apply one_div_le_one_div_of_le (by positivity)
      dsimp [f]
      linarith [Nat.floor_le (hnonneg t ht)]
    _ = ∑ k ∈ S.image f, 1 / (1 + (k : ℝ)) := himage.symm
    _ ≤ ∑ k ∈ Finset.range M, 1 / (1 + (k : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = (harmonic M : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    _ ≤ 1 + Real.log M := harmonic_le_one_add_log M

/-- Pages 22 and 23, spacing detail: For real points separated by at least 1 and with absolute value below a natural M, the reciprocal first-power sum is at most twice 1 plus log M. -/
theorem spaced_harmonic_sum (S : Finset ℝ) (M0 : ℕ)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|)
    (hbound : ∀ t ∈ S, |t| < (M0 : ℝ)) :
    ∑ t ∈ S, 1 / (1 + |t|) ≤ 2 * (1 + Real.log M0) := by
  let P := S.filter (fun t => 0 ≤ t)
  let M := S.filter (fun t => t < 0)
  let Q := M.image (fun t => -t)
  have hpos : (∑ t ∈ P, 1 / (1 + |t|)) ≤ 1 + Real.log M0 := by
    have hh := nonnegative_spaced_harmonic P M0
      (fun t ht => (Finset.mem_filter.mp ht).2)
      (fun t ht u hu hne => hspace t (Finset.mem_filter.mp ht).1
        u (Finset.mem_filter.mp hu).1 hne)
      (fun t ht => lt_of_le_of_lt (le_abs_self t) (hbound t (Finset.mem_filter.mp ht).1))
    convert hh using 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [abs_of_nonneg (Finset.mem_filter.mp ht).2]
  have hQnonneg : ∀ t ∈ Q, 0 ≤ t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    have := (Finset.mem_filter.mp hu).2
    linarith
  have hQspace : ∀ t ∈ Q, ∀ u ∈ Q, t ≠ u → 1 ≤ |t - u| := by
    intro t ht u hu hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    have hab : a ≠ b := by intro heq; exact hne (by rw [heq])
    have hh := hspace a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hneg : (∑ t ∈ M, 1 / (1 + |t|)) ≤ 1 + Real.log M0 := by
    have hQbound : ∀ t ∈ Q, t < (M0 : ℝ) := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      have hb := hbound u (Finset.mem_filter.mp hu).1
      simpa only [abs_of_neg (Finset.mem_filter.mp hu).2] using hb
    have hh := nonnegative_spaced_harmonic Q M0 hQnonneg hQspace hQbound
    have heq : (∑ t ∈ Q, 1 / (1 + t)) = ∑ t ∈ M, 1 / (1 + |t|) := by
      rw [show Q = M.image (fun t => -t) from rfl, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro t ht
        rw [abs_of_neg (Finset.mem_filter.mp ht).2]
      · intro a ha b hb heq
        exact neg_injective heq
    rw [heq] at hh
    exact hh
  have hsplit : (∑ t ∈ S, 1 / (1 + |t|)) =
      (∑ t ∈ P, 1 / (1 + |t|)) + (∑ t ∈ M, 1 / (1 + |t|)) := by
    simpa only [P, M, not_le] using
      (Finset.sum_filter_add_sum_filter_not S (fun t => 0 ≤ t) (fun t => 1 / (1 + |t|))).symm
  linarith

/-- Pages 22 and 23, spacing detail: For real points separated by at least 1 and within distance M of u, the sum of one divided by one plus the distance to u is at most twice 1 plus log M. -/
theorem shifted_spaced_harmonic (S : Finset ℝ) (u : ℝ) (M : ℕ)
    (hspace : ∀ t ∈ S, ∀ v ∈ S, t ≠ v → 1 ≤ |t - v|)
    (hbound : ∀ t ∈ S, |t - u| < (M : ℝ)) :
    ∑ t ∈ S, 1 / (1 + |t - u|) ≤ 2 * (1 + Real.log M) := by
  let X := S.image (fun t => t - u)
  have hinj : Set.InjOn (fun t : ℝ => t - u) S := by
    intro t ht v hv heq
    linarith
  have hXspace : ∀ t ∈ X, ∀ v ∈ X, t ≠ v → 1 ≤ |t - v| := by
    intro t ht v hv hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    have hab : a ≠ b := by intro heq; exact hne (by rw [heq])
    simpa only [sub_sub_sub_cancel_right] using hspace a ha b hb hab
  have hXbound : ∀ t ∈ X, |t| < (M : ℝ) := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    exact hbound a ha
  have hh := spaced_harmonic_sum X M hXspace hXbound
  simpa only [X, Finset.sum_image hinj] using hh

/-- Pages 22 and 23, spacing detail: For points separated by at least 1 in the interval from minus T to T, and u of absolute value at most 2T, the reciprocal distance sum is at most 10 log x when x is at least 2 and 0 at most T at most x. -/
theorem kernel_le_ten_log (S : Finset ℝ) {x T u : ℝ} (hx : 2 ≤ x)
    (hT0 : 0 ≤ T) (hTx : T ≤ x)
    (hspace : ∀ t ∈ S, ∀ v ∈ S, t ≠ v → 1 ≤ |t - v|)
    (hS : ∀ t ∈ S, |t| ≤ T) (hu : |u| ≤ 2 * T) :
    ∑ t ∈ S, 1 / (1 + |t - u|) ≤ 10 * Real.log x := by
  let M : ℕ := ⌈3 * T⌉₊ + 1
  have hbound : ∀ t ∈ S, |t - u| < (M : ℝ) := by
    intro t ht
    have htri : |t - u| ≤ |t| + |u| := by
      simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le t 0 u)
    have hceil := Nat.le_ceil (3 * T)
    dsimp [M]
    push_cast
    linarith [hS t ht]
  have hMpos : (0 : ℝ) < M := by dsimp [M]; positivity
  have hMx : (M : ℝ) ≤ x ^ 3 := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 3 * T by linarith)
    have hx0 : 0 ≤ x := by linarith
    have hsq : 0 ≤ x ^ 2 - 4 := by nlinarith
    dsimp [M]
    push_cast
    nlinarith [mul_nonneg hx0 hsq]
  have hlogM : Real.log (M : ℝ) ≤ 3 * Real.log x := by
    have hh := Real.log_le_log hMpos hMx
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hhalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hh := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hx
    linarith [Real.log_two_gt_d9]
  have hh := shifted_spaced_harmonic S u M hspace hbound
  linarith

end LeanLab.BHP1997.Spacing132
