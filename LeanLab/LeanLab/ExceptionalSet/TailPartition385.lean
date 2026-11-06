import LeanLab.ExceptionalSet.PrimeEnergy385

/-!
The infinite unit interval summation on P0082 page 365 before display 24.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.TailPartition385

open Real MeasureTheory Set Filter

/-- An integrable function on a half line splits into its consecutive unit blocks.
Source: P0082 page 365, summation over k before display 24. -/
theorem hasSum_Ioi_blocks (f : ℝ → ℝ) (hf : Integrable f) (a : ℝ) :
    HasSum (fun n : ℕ => ∫ x in a + n..a + n + 1, f x) (∫ x in Ioi a, f x) := by
  have hu : (⋃ n : ℕ, Ioc (a + n) (a + n + 1)) = Ioi a := by
    have hmin (n : ℕ) : a + (0 : ℕ) ≤ a + n := by
      simpa only [Nat.cast_zero, add_zero] using
        (le_add_of_nonneg_right (Nat.cast_nonneg n) : a ≤ a + (n : ℝ))
    have hnb : ¬ BddAbove (range (fun n : ℕ => a + (n : ℝ))) := by
      rintro ⟨b, hb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (b - a)
      have hle := hb (mem_range_self n)
      linarith
    simpa only [bot_eq_zero, Nat.cast_zero, add_zero, Order.succ_eq_add_one,
      Nat.cast_add, Nat.cast_one, add_assoc] using
      (iUnion_Ioc_map_succ_eq_Ioi hmin hnb)
  have hd : Pairwise (fun i j : ℕ => Disjoint (Ioc (a + i) (a + i + 1)) (Ioc (a + j) (a + j + 1))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
      apply disjoint_left.mpr
      intro x hi hj
      have := hi.2
      have := hj.1
      linarith
    · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
      apply disjoint_left.mpr
      intro x hi hj
      have := hi.1
      have := hj.2
      linarith
  have hs : HasSum (fun n : ℕ => ∫ x in a + n..a + n + 1, f x) (∫ x in Ioi a, f x) := by
    simp_rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right zero_le_one)]
    rw [← hu]
    exact hasSum_integral_iUnion (fun _ => measurableSet_Ioc) hd hf.integrableOn
  exact hs

/-- The half line integral is the sum of its unit blocks, P0082 page 365. -/
theorem integral_Ioi_eq_tsum_blocks (f : ℝ → ℝ) (hf : Integrable f) (a : ℝ) :
    (∫ x in Ioi a, f x) = ∑' n : ℕ, ∫ x in a + n..a + n + 1, f x :=
  (hasSum_Ioi_blocks f hf a).tsum_eq.symm

/-- The inverse square tail used on P0082 page 365 before display 24. -/
theorem reciprocal_square_tail (K : ℕ) (hK : 2 ≤ K) :
    (∑' n : ℕ, 1 / (((n + K : ℕ) : ℝ) ^ 2)) ≤ 1 / ((K : ℝ) - 1) := by
  have hc : 0 < ((K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K - 1)
  have ha : AntitoneOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ici ((K - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hc.trans_le hx) hxy (by norm_num)
  have hi : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi ((K - 1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  have hn : ∀ x ∈ Ioi ((K - 1 : ℕ) : ℝ), 0 ≤ x ^ (-2 : ℝ) :=
    fun x hx => Real.rpow_nonneg (hc.trans hx).le _
  have hs := AntitoneOn.tsum_comp_add_le_integral (K - 1) ha hi hn
  have he (n : ℕ) : (((n + (K - 1) + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) =
      1 / (((n + K : ℕ) : ℝ) ^ 2) := by
    rw [show n + (K - 1) + 1 = n + K by omega,
      Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, one_div]
  simp_rw [he] at hs
  rw [integral_Ioi_rpow_of_lt (by norm_num) hc] at hs
  norm_num [Real.rpow_neg_one] at hs
  simpa [Nat.cast_sub (show 1 ≤ K by omega), one_div] using hs

/-- A uniform inverse square unit bound gives the half line integral estimate.
Source: P0082 page 365, the summation before display 24. -/
theorem integral_Ioi_le_of_blocks (f : ℝ → ℝ) (hf : Integrable f)
    (K : ℕ) (hK : 2 ≤ K) (A : ℝ) (hA : 0 ≤ A)
    (hblock : ∀ k : ℕ, K ≤ k → (∫ x in (k : ℝ)..(k : ℝ) + 1, f x) ≤ A / (k : ℝ) ^ 2) :
    (∫ x in Ioi (K : ℝ), f x) ≤ A / ((K : ℝ) - 1) := by
  have hs : Summable (fun n : ℕ => 1 / (((n + K : ℕ) : ℝ) ^ 2)) := by
    exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (fun i j h => by omega)
  have hsA : Summable (fun n : ℕ => A / (((n + K : ℕ) : ℝ) ^ 2)) := by
    simpa only [mul_one_div] using hs.mul_left A
  have hl := hasSum_Ioi_blocks f hf (K : ℝ)
  have hp (n : ℕ) : (∫ x in (K : ℝ) + n..(K : ℝ) + n + 1, f x) ≤
      A / (((n + K : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      hblock (n + K) (by omega)
  calc (∫ x in Ioi (K : ℝ), f x)
      = ∑' n : ℕ, ∫ x in (K : ℝ) + n..(K : ℝ) + n + 1, f x := hl.tsum_eq.symm
    _ ≤ ∑' n : ℕ, A / (((n + K : ℕ) : ℝ) ^ 2) := Summable.tsum_le_tsum hp hl.summable hsA
    _ = A * ∑' n : ℕ, 1 / (((n + K : ℕ) : ℝ) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    _ ≤ A * (1 / ((K : ℝ) - 1)) := mul_le_mul_of_nonneg_left (reciprocal_square_tail K hK) hA
    _ = _ := by ring

end LeanLab.ExceptionalSet.TailPartition385
