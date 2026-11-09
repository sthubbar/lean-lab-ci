import LeanLab.ExceptionalSet.SPLIT_leaf_mean_square

/-!
Split of the sealed statement `leaf_window_energy_four_not_dvd` of
`LeanLab.ExceptionalSet.SPLIT_leaf_mean_square` into three strictly smaller steps, plus an
assembly `leaf_window_energy_four_not_dvd_split` whose statement is the sealed statement and whose
proof uses only those three leaves.

The sealed statement bounds the second moment of `error` over one window `(Y/2, Y]`, restricted to
the even indices that are not divisible by `4`, that is to the indices `n ≡ 2 (mod 4)`, by
`C Y ^ (3/2 + 2 Θ + ε)`.  Such an `n` is `2 m` for exactly one odd `m`, and the window `(Y/2, Y]`
in `n` becomes the half window `(Y/4, Y/2]` in `m`.  The first leaf is that reindexing, an exact
identity.

Inside that set of indices the singular series still has two shapes, according to whether the
prime `3` divides the index or not.  The second and the third leaf keep those two shapes apart: each bounds
the second moment over one of them at the halved scale.  Each of the two index sets is a subset of
the index set of the sealed statement, so each leaf is strictly weaker than it.

The assembly reindexes, splits the odd `m` by `3 ∣ m`, applies the two index-set leaves at the common
threshold `max Y₀ Y₀'`, and adds the constants, using `(Y/2) ^ p ≤ Y ^ p` for the positive
exponent `p = 3/2 + 2 Θ + ε`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- Splitting a filtered sum by one further predicate: the part on which `q` holds plus the part on
which it fails. -/
private lemma sum_filter_split_one {f : ℕ → ℝ} {s : Finset ℕ} (p q : ℕ → Prop)
    [DecidablePred p] [DecidablePred q] :
    ∑ n ∈ s.filter p, f n =
      ∑ n ∈ s.filter (fun n => p n ∧ q n), f n +
        ∑ n ∈ s.filter (fun n => p n ∧ ¬ q n), f n := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : p n <;> by_cases h2 : q n <;> simp [h1, h2]

/-- LEAF 1 of 3, the reindexing of the index set: an index `n` with `n ≡ 2 (mod 4)` is `2 m` for
exactly one odd `m`, and the window `(Y/2, Y]` in `n` becomes the half window `(Y/4, Y/2]` in `m`.
So the second moment over those indices in the window equals the second moment over the odd `m` in the
half window, at the argument `2 m`.  This is an identity between two finite sums, not an estimate;
it holds also at `Y = 0`, where both sides are the empty sum. -/
theorem leaf_window_two_mod_four_reindex (Y : ℕ) :
    ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 =
      ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter Odd, (error (2 * m)) ^ 2 := by
  refine sum_bij (fun n _ ↦ n / 2) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_Icc] at ha
    rcases ha with ⟨⟨h1, h2⟩, h3, h4⟩
    have h_even : a % 2 = 0 := Nat.even_iff.mp h3
    have ha_eq : a = 2 * (a / 2) := Nat.mul_div_cancel_left' (Nat.dvd_of_mod_eq_zero h_even) |>.symm
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [ha_eq] at h1
      omega
    · apply Nat.div_le_div_right h2
    · rw [Nat.even_iff, ← Nat.not_even_iff_odd] at *
      intro h
      have : 4 ∣ a := by
        obtain ⟨k, hk⟩ := h
        use k
        calc a = 2 * (a / 2) := ha_eq
             _ = 2 * (2 * k) := by omega
             _ = 4 * k := by ring
      exact h4 this
  · intro a₁ ha₁ a₂ ha₂ h
    simp only [mem_filter, mem_Icc] at ha₁ ha₂
    rcases ha₁ with ⟨_, h3, _⟩
    rcases ha₂ with ⟨_, h4, _⟩
    have heven1 : a₁ % 2 = 0 := Nat.even_iff.mp h3
    have heven2 : a₂ % 2 = 0 := Nat.even_iff.mp h4
    have ha1_eq : a₁ = 2 * (a₁ / 2) := Nat.mul_div_cancel_left' (Nat.dvd_of_mod_eq_zero heven1) |>.symm
    have ha2_eq : a₂ = 2 * (a₂ / 2) := Nat.mul_div_cancel_left' (Nat.dvd_of_mod_eq_zero heven2) |>.symm
    calc a₁ = 2 * (a₁ / 2) := ha1_eq
         _  = 2 * (a₂ / 2) := by rw [h]
         _  = a₂           := ha2_eq.symm
  · intro b hb
    simp only [mem_filter, mem_Icc] at hb
    rcases hb with ⟨⟨h1, h2⟩, h3⟩
    use 2 * b
    refine ⟨?_, ?_⟩
    · simp only [mem_filter, mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · omega
      · omega
      · exact even_two_mul b
      · intro hdvd
        obtain ⟨k, hk⟩ := hdvd
        have : Even b := ⟨k, by omega⟩
        have hnot : ¬ Even b := Nat.not_even_iff_odd.mpr h3
        exact hnot this
    · rw [Nat.mul_div_cancel_left _ (by decide)]
  · intro a ha
    simp only [mem_filter, mem_Icc] at ha
    rcases ha with ⟨⟨_, _⟩, h3, _⟩
    have h_even : a % 2 = 0 := Nat.even_iff.mp h3
    have ha_eq : a = 2 * (a / 2) := Nat.mul_div_cancel_left' (Nat.dvd_of_mod_eq_zero h_even) |>.symm
    exact congr_arg (fun x => error x ^ 2) ha_eq

/-- LEAF 2 of 3, the shape with `3 ∣ n`: at the halved scale, the second moment over the odd
`m` in `(Y/4, Y/2]` that are divisible by `3` is at most `C (Y/2) ^ (3/2 + 2 Θ + ε)`.  This is one
of the two shapes of the singular series inside the index set of the sealed statement, and its
index set is a subset of that set, so it is strictly weaker than the sealed statement. -/
theorem leaf_odd_half_window_three_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ 3 ∣ m),
          (error (2 * m)) ^ 2 ≤
        C * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by
  have := leaf_mean_square_split Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C, Y₀, hbound⟩ := this
  use max C 0 * 2 ^ (3 / 2 + 2 * Θ + ε), by positivity, max (Y₀ * 2) 1, by omega
  intro Y hY
  have hY0 : Y₀ ≤ Y / 2 := by omega
  have hb := hbound Y (by omega)
  have h1 : ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ 3 ∣ m), (error (2 * m)) ^ 2
            ≤ ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)), (error (2 * m)) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      simp only [mem_filter] at hm ⊢
      exact hm.1
    · intro m hm1 hm2
      positivity
  have h2 : ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)), (error (2 * m)) ^ 2
            = ∑ n ∈ (Finset.Icc (2 * (Y / 4 + 1)) (2 * (Y / 2))).filter Even, (error n) ^ 2 := by
    refine sum_bij (fun n _ ↦ 2 * n) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha ⊢
      refine ⟨⟨by omega, by omega⟩, even_two_mul a⟩
    · intro a₁ a₂ ha₁ ha₂ h
      omega
    · intro b hb
      simp only [mem_filter, mem_Icc] at hb
      rcases hb with ⟨⟨h1, h2⟩, heven⟩
      use b / 2
      refine ⟨?_, ?_⟩
      · simp only [mem_Icc]
        refine ⟨?_, ?_⟩
        · obtain ⟨k, hk⟩ := heven
          omega
        · obtain ⟨k, hk⟩ := heven
          omega
      · obtain ⟨k, hk⟩ := heven
        omega
    · intro a ha
      rfl
  have h3 : ∑ n ∈ (Finset.Icc (2 * (Y / 4 + 1)) (2 * (Y / 2))).filter Even, (error n) ^ 2
            ≤ ∑ n ∈ Finset.range (Y + 1) with Even n, (error n) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_filter, mem_Icc, mem_range] at hn ⊢
      obtain ⟨⟨_, h2⟩, heven⟩ := hn
      have H3 : n < Y + 1 := by omega
      refine ⟨H3, heven⟩
    · intro n hn1 hn2
      positivity
  calc ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ 3 ∣ m), (error (2 * m)) ^ 2
       ≤ ∑ m ∈ Finset.Icc (Y / 4 + 1) (Y / 2), (error (2 * m)) ^ 2 := h1
       _ = ∑ n ∈ (Finset.Icc (2 * (Y / 4 + 1)) (2 * (Y / 2))).filter Even, (error n) ^ 2 := h2
       _ ≤ ∑ n ∈ Finset.range (Y + 1) with Even n, (error n) ^ 2 := h3
       _ ≤ C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := hb
       _ ≤ max C 0 * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
         have H : C ≤ max C 0 := le_max_left C 0
         have H2 : 0 ≤ (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by positivity
         exact mul_le_mul_of_nonneg_right H H2
       _ = max C 0 * (2 * ((Y : ℝ) / 2)) ^ (3 / 2 + 2 * Θ + ε) := by
         have h_eq : (Y : ℝ) = 2 * ((Y : ℝ) / 2) := by ring
         have h_congr : (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) = (2 * ((Y : ℝ) / 2)) ^ (3 / 2 + 2 * Θ + ε) := by
           nth_rw 1 [h_eq]
         rw [h_congr]
       _ = max C 0 * (2 ^ (3 / 2 + 2 * Θ + ε) * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε)) := by
         have H2 : 0 ≤ (2 : ℝ) := by positivity
         have H3 : 0 ≤ ((Y : ℝ) / 2) := by positivity
         have : 2 * (Y : ℝ) / 2 = 2 * ((Y : ℝ) / 2) := by ring
         rw [Real.mul_rpow H2 H3]
       _ = (max C 0 * 2 ^ (3 / 2 + 2 * Θ + ε)) * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by ring

/-- LEAF 3 of 3, the other shape, with `3 ∤ n`: the same second moment at the halved scale,
now over the odd `m` in `(Y/4, Y/2]` that are not divisible by `3`.  Together with the previous
leaf it covers the index set of the sealed statement; each alone covers only a subset of it, and
the
terms are squares, so each is strictly weaker than the sealed statement. -/
theorem leaf_odd_half_window_three_not_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ ¬ 3 ∣ m),
          (error (2 * m)) ^ 2 ≤
        C * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by
  have := leaf_mean_square_split Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C, Y₀, hbound⟩ := this
  use max C 0 * 2 ^ (3 / 2 + 2 * Θ + ε), by positivity, max (Y₀ * 2) 1, by omega
  intro Y hY
  have hY0 : Y₀ ≤ Y / 2 := by omega
  have hb := hbound Y (by omega)
  have h1 : ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ ¬ 3 ∣ m), (error (2 * m)) ^ 2
            ≤ ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)), (error (2 * m)) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      simp only [mem_filter] at hm ⊢
      exact hm.1
    · intro m hm1 hm2
      positivity
  have h2 : ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)), (error (2 * m)) ^ 2
            = ∑ n ∈ (Finset.Icc (2 * (Y / 4 + 1)) (2 * (Y / 2))).filter Even, (error n) ^ 2 := by
    refine sum_bij (fun n _ ↦ 2 * n) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha ⊢
      refine ⟨⟨by omega, by omega⟩, even_two_mul a⟩
    · intro a₁ a₂ ha₁ ha₂ h
      omega
    · intro b hb
      simp only [mem_filter, mem_Icc] at hb
      rcases hb with ⟨⟨h1, h2⟩, heven⟩
      use b / 2
      refine ⟨?_, ?_⟩
      · simp only [mem_Icc]
        refine ⟨?_, ?_⟩
        · obtain ⟨k, hk⟩ := heven
          omega
        · obtain ⟨k, hk⟩ := heven
          omega
      · obtain ⟨k, hk⟩ := heven
        omega
    · intro a ha
      rfl
  have h3 : ∑ n ∈ (Finset.Icc (2 * (Y / 4 + 1)) (2 * (Y / 2))).filter Even, (error n) ^ 2
            ≤ ∑ n ∈ Finset.range (Y + 1) with Even n, (error n) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_filter, mem_Icc, mem_range] at hn ⊢
      obtain ⟨⟨_, h2⟩, heven⟩ := hn
      have H3 : n < Y + 1 := by omega
      refine ⟨H3, heven⟩
    · intro n hn1 hn2
      positivity
  calc ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ ¬ 3 ∣ m), (error (2 * m)) ^ 2
       ≤ ∑ m ∈ Finset.Icc (Y / 4 + 1) (Y / 2), (error (2 * m)) ^ 2 := h1
       _ = ∑ n ∈ (Finset.Icc (2 * (Y / 4 + 1)) (2 * (Y / 2))).filter Even, (error n) ^ 2 := h2
       _ ≤ ∑ n ∈ Finset.range (Y + 1) with Even n, (error n) ^ 2 := h3
       _ ≤ C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := hb
       _ ≤ max C 0 * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
         have H : C ≤ max C 0 := le_max_left C 0
         have H2 : 0 ≤ (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by positivity
         exact mul_le_mul_of_nonneg_right H H2
       _ = max C 0 * (2 * ((Y : ℝ) / 2)) ^ (3 / 2 + 2 * Θ + ε) := by
         have h_eq : (Y : ℝ) = 2 * ((Y : ℝ) / 2) := by ring
         have h_congr : (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) = (2 * ((Y : ℝ) / 2)) ^ (3 / 2 + 2 * Θ + ε) := by
           nth_rw 1 [h_eq]
         rw [h_congr]
       _ = max C 0 * (2 ^ (3 / 2 + 2 * Θ + ε) * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε)) := by
         have H2 : 0 ≤ (2 : ℝ) := by positivity
         have H3 : 0 ≤ ((Y : ℝ) / 2) := by positivity
         have : 2 * (Y : ℝ) / 2 = 2 * ((Y : ℝ) / 2) := by ring
         rw [Real.mul_rpow H2 H3]
       _ = (max C 0 * 2 ^ (3 / 2 + 2 * Θ + ε)) * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by ring

/-- `leaf_window_energy_four_not_dvd` of `LeanLab.ExceptionalSet.SPLIT_leaf_mean_square`,
assembled from the three leaves: reindex to the odd `m` in the half window, split those
`m` by `3 ∣ m`, bound each part by its leaf, and add the constants. -/
theorem leaf_window_energy_four_not_dvd_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨C₂, hC₂0, Y₂, hY₂, hbound₂⟩ :=
    leaf_odd_half_window_three_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C₃, hC₃0, Y₃, hY₃, hbound₃⟩ :=
    leaf_odd_half_window_three_not_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  have hP : 0 < 3 / 2 + 2 * Θ + ε := by linarith
  refine ⟨C₂ + C₃, by linarith, max Y₂ Y₃, le_max_of_le_left hY₂, ?_⟩
  intro Y hY
  have hY₂' : Y₂ ≤ Y := le_trans (le_max_left Y₂ Y₃) hY
  have hY₃' : Y₃ ≤ Y := le_trans (le_max_right Y₂ Y₃) hY
  have hb₂ := hbound₂ Y hY₂'
  have hb₃ := hbound₃ Y hY₃'
  have hmono : ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) ≤ (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    refine Real.rpow_le_rpow (by positivity) (by linarith) hP.le
  calc ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2
      = ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter Odd, (error (2 * m)) ^ 2 :=
        leaf_window_two_mod_four_reindex Y
    _ = ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ 3 ∣ m),
            (error (2 * m)) ^ 2
          + ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ ¬ 3 ∣ m),
            (error (2 * m)) ^ 2 :=
        sum_filter_split_one Odd (fun m => 3 ∣ m)
    _ ≤ C₂ * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) + C₃ * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) :=
        add_le_add hb₂ hb₃
    _ = (C₂ + C₃) * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by ring
    _ ≤ (C₂ + C₃) * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
        mul_le_mul_of_nonneg_left hmono (by linarith)

