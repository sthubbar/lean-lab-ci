/-
Finite weighted counting inputs for P0079 page 4.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.KernelFourier293

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, definition of N. The solution set in a fixed box is finite. -/
theorem counted_set_finite293 {s : ℕ} (l1 l2 : ℝ) (μ : Fin s → ℝ) (γ η ε X : ℝ) :
    {x ∈ Sol l1 l2 μ γ η | ε * X ≤ x.1 ∧ (x.1 : ℝ) ≤ X ∧ ε * X ≤ x.2.1 ∧
      (x.2.1 : ℝ) ≤ X ∧ ∀ i, (x.2.2 i : ℝ) ≤ logb 2 (ε * X / (2 * ∑ j, |μ j|))}.Finite := by
  let L := logb 2 (ε * X / (2 * ∑ j, |μ j|))
  have hfun : {m : Fin s → ℕ | ∀ i, m i ≤ ⌊L⌋₊}.Finite := by
    apply (Set.finite_range (fun m : Fin s → Fin (⌊L⌋₊ + 1) => fun i => (m i : ℕ))).subset
    intro m hm
    exact ⟨(fun i => ⟨m i, Nat.lt_succ_of_le (hm i)⟩), rfl⟩
  apply ((Set.finite_Iic ⌊X⌋₊).prod ((Set.finite_Iic ⌊X⌋₊).prod hfun)).subset
  intro x hx
  exact ⟨Nat.le_floor hx.2.2.1, Nat.le_floor hx.2.2.2.2.1,
    fun i => Nat.le_floor (hx.2.2.2.2.2 i)⟩

/-- P0079 page 4, the weighted counting inequality before display 13.
Any finite collection of candidate prime tuples contributes at most eta log squared X
per counted solution. The collection need not contain every candidate. -/
theorem weighted_count_le293 {s : ℕ} (l1 l2 : ℝ) (μ : Fin s → ℝ) (γ η ε X : ℝ)
    (hη : 0 < η) (hX : 2 ≤ X) (T : Finset (ℕ × ℕ × (Fin s → ℕ)))
    (hT : ∀ x ∈ T, x.1.Prime ∧ x.2.1.Prime ∧ (∀ i, 1 ≤ x.2.2 i) ∧
      ε * X ≤ x.1 ∧ (x.1 : ℝ) ≤ X ∧ ε * X ≤ x.2.1 ∧ (x.2.1 : ℝ) ≤ X ∧
      ∀ i, (x.2.2 i : ℝ) ≤ logb 2 (ε * X / (2 * ∑ j, |μ j|))) :
    ∑ x ∈ T, log x.1 * log x.2.1 * max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|) ≤
      η * (log X) ^ 2 * NX l1 l2 μ γ η ε X := by
  let S := T.filter (fun x => |form l1 l2 μ γ x.1 x.2.1 x.2.2| < η)
  let w := fun x : ℕ × ℕ × (Fin s → ℕ) =>
    log x.1 * log x.2.1 * max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|)
  have hsum : ∑ x ∈ T, w x = ∑ x ∈ S, w x := by
    symm
    dsimp only [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    split_ifs with h
    · rfl
    · have hz : max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|) = 0 :=
        max_eq_left (by linarith [le_of_not_gt h])
      simp [w, hz]
  have hweight : ∀ x ∈ S, w x ≤ η * (log X) ^ 2 := by
    intro x hx
    obtain ⟨hp1, hp2, hm, hlow1, hupp1, hlow2, hupp2, hcut⟩ := hT x (mem_filter.mp hx).1
    have hp1' : (1 : ℝ) ≤ x.1 := by exact_mod_cast hp1.one_lt.le
    have hp2' : (1 : ℝ) ≤ x.2.1 := by exact_mod_cast hp2.one_lt.le
    have hlog1 := log_nonneg hp1'
    have hlog2 := log_nonneg hp2'
    have hlogX : 0 ≤ log X := log_nonneg (by linarith)
    have hlog1X : log x.1 ≤ log X := log_le_log (by linarith) hupp1
    have hlog2X : log x.2.1 ≤ log X := log_le_log (by linarith) hupp2
    have htent : max 0 (η - |form l1 l2 μ γ x.1 x.2.1 x.2.2|) ≤ η :=
      max_le hη.le (by linarith [abs_nonneg (form l1 l2 μ γ x.1 x.2.1 x.2.2)])
    calc
      w x ≤ (log X * log X) * η :=
        mul_le_mul (mul_le_mul hlog1X hlog2X hlog2 hlogX) htent
          (le_max_left _ _) (mul_nonneg hlogX hlogX)
      _ = _ := by ring
  have hcard : S.card ≤ NX l1 l2 μ γ η ε X := by
    rw [← Set.ncard_coe_finset S]
    apply Set.ncard_le_ncard (ht := counted_set_finite293 l1 l2 μ γ η ε X)
    intro x hx
    have hxs := mem_filter.mp hx
    obtain ⟨hp1, hp2, hm, hlow1, hupp1, hlow2, hupp2, hcut⟩ := hT x hxs.1
    exact ⟨⟨hp1, hp2, hm, hxs.2⟩, hlow1, hupp1, hlow2, hupp2, hcut⟩
  calc
    _ = ∑ x ∈ S, w x := hsum
    _ ≤ ∑ _ ∈ S, η * (log X) ^ 2 := sum_le_sum hweight
    _ = (S.card : ℝ) * (η * (log X) ^ 2) := by simp
    _ ≤ (NX l1 l2 μ γ η ε X : ℝ) * (η * (log X) ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

/-- P0079 page 4, definition of the additive character. Addition of phases
is multiplication of characters. -/
theorem character_add293 (x y : ℝ) : character293 (x + y) = character293 x * character293 y := by
  unfold character293
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0079 page 4, expansion of the product of power sums. A finite phase sum
has character equal to the product of its characters. -/
theorem character_sum293 {ι : Type*} (T : Finset ι) (φ : ι → ℝ) :
    character293 (∑ i ∈ T, φ i) = ∏ i ∈ T, character293 (φ i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [character293]
  | @insert a T ha ih => simp [ha, character_add293, ih]

/-- P0079 page 4, displays 11 to 13. A finite weighted exponential sum
integrates term by term against the kernel to the weighted tent sum. -/
theorem finite_kernel_integral293 {ι : Type*} (T : Finset ι) (w : ι → ℂ) (φ : ι → ℝ)
    (η : ℝ) (hη : 0 < η) :
    (∫ α : ℝ, (∑ i ∈ T, w i * character293 (φ i * α)) * (kernel293 η α : ℂ)) =
      ∑ i ∈ T, w i * ((max 0 (η - |φ i|) : ℝ) : ℂ) := by
  simp_rw [sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [integral_const_mul, kernel_transform293 η (φ i) hη]
  · intro i hi
    exact (kernel_character_integrable293 η (φ i)).const_mul (w i)

end LeanLab.LZPowersOfTwo
