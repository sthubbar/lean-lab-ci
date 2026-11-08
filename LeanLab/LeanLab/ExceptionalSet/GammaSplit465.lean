import LeanLab.ExceptionalSet.GammaTail465

/-!
P0082 page361 display17, separating the finite and far portions of Gamma2.
The proof uses positive partial sums, with the convergence bound explicit.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset

/-- P0082 page361 display17 and page362 display19. For a nonzero m,
Gamma2 is at most its finite portion through Y plus the explicit far
divisor tail. No sparse sequence distribution estimate is assumed. -/
theorem gammaTwo_split_bound (r : ℕ) (P : ℝ) (hP : 0 ≤ P) (m : ℤ) (hm : m ≠ 0)
    (Y : ℕ) (hY : 1 ≤ Y) :
    (r : ℝ) * (∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) ≤
        (r : ℝ) * (∑ q ∈ (Ioc ⌊P⌋₊ Y).filter (fun q => r ∣ q),
          1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))) +
        (r : ℝ) * (4 * (6 + 2 * Real.log Y) * (m.natAbs.divisors.card : ℝ) ^ 2 / Y) := by
  classical
  let f := fun q : ℕ => if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0
  have hnonneg (q : ℕ) : 0 ≤ f q := by dsimp [f]; split_ifs <;> positivity
  have hbound : (∑' q : ℕ, f q) ≤
      (∑ q ∈ (Ioc ⌊P⌋₊ Y).filter (fun q => r ∣ q),
        1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))) +
      4 * (6 + 2 * Real.log Y) * (m.natAbs.divisors.card : ℝ) ^ 2 / Y := by
    apply Real.tsum_le_of_sum_range_le hnonneg
    intro M
    have hnear : ∑ q ∈ (range M).filter (fun q => q ≤ Y), f q ≤
        ∑ q ∈ (Ioc ⌊P⌋₊ Y).filter (fun q => r ∣ q),
          1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) := by
      dsimp only [f]
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨hinside, hguard⟩ := mem_filter.mp hq
        have hqY := (mem_filter.mp hinside).2
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt hP).mpr hguard.1, hqY⟩, hguard.2⟩
      · intro q _ _
        positivity
    have hfar : ∑ q ∈ (range M).filter (fun q => ¬ q ≤ Y), f q ≤
        4 * (6 + 2 * Real.log Y) * (m.natAbs.divisors.card : ℝ) ^ 2 / Y := by
      have hmono : ∑ q ∈ (range M).filter (fun q => ¬ q ≤ Y), f q ≤
          ∑ q ∈ (range M).filter (fun q => ¬ q ≤ Y),
            1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) := by
        apply sum_le_sum
        intro q _
        dsimp [f]
        split_ifs <;> first | exact le_rfl | positivity
      refine hmono.trans ((sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)).trans
        (far_totient_kernel_sum_le m hm Y M hY))
      intro q hq
      obtain ⟨hqr, hqY⟩ := mem_filter.mp hq
      exact mem_Ioc.mpr ⟨by omega, (mem_range.mp hqr).le⟩
    rw [← sum_filter_add_sum_filter_not (range M) (fun q => q ≤ Y) f]
    exact add_le_add hnear hfar
  calc
    _ ≤ (r : ℝ) * ((∑ q ∈ (Ioc ⌊P⌋₊ Y).filter (fun q => r ∣ q),
        1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))) +
        4 * (6 + 2 * Real.log Y) * (m.natAbs.divisors.card : ℝ) ^ 2 / Y) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
