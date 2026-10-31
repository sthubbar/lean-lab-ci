/-
P0069, page 2, the interval covering implicit in the deduction of
Theorem 1 from display 1.2. These are elementary covering details.
Mathlib supplies finite union bounds, real powers and Nat.find.
AI wrote the Lean code. CODEX task132, 2026-10-26.
-/
import LeanLab.BHP1997.Statements

namespace LeanLab.BHP1997.Decomp132
open Classical Real Filter

/-- Page 2, interval covering detail: Every point between the first and last endpoints of a nonempty finite chain lies in one adjacent interval. -/
theorem mesh_cover (y : ℕ → ℝ) {K : ℕ} (hK : 0 < K) {z : ℝ}
    (hz0 : y 0 ≤ z) (hzK : z ≤ y K) :
    ∃ i : ℕ, i < K ∧ y i ≤ z ∧ z ≤ y (i + 1) := by
  induction K with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      exact ⟨0, by omega, hz0, hzK⟩
    · by_cases hz : z ≤ y k
      · obtain ⟨i, hi, h1, h2⟩ := ih (by omega) hz
        exact ⟨i, by omega, h1, h2⟩
      · exact ⟨k, by omega, le_of_not_ge hz, hzK⟩

/-- Page 2, interval covering detail: For x at least 1 and z greater than x, consecutive steps of length y to delta reach z in finitely many steps. The last endpoint is at most z plus z to delta. -/
theorem power_mesh {x z δ : ℝ} (hx : 1 ≤ x) (hxz : x < z) (hδ : 0 ≤ δ) :
    ∃ (y : ℕ → ℝ) (K : ℕ), 0 < K ∧ y 0 = x ∧
      (∀ i, y (i + 1) = y i + (y i) ^ δ) ∧
      (∀ i, x ≤ y i) ∧ z ≤ y K ∧ y K ≤ z + z ^ δ := by
  let y : ℕ → ℝ := fun n => (fun t : ℝ => t + t ^ δ)^[n] x
  have hy0 : y 0 = x := rfl
  have hstep (n : ℕ) : y (n + 1) = y n + (y n) ^ δ := by
    exact Function.iterate_succ_apply' _ n x
  have hlin (n : ℕ) : x + n ≤ y n := by
    induction n with
    | zero => simp [hy0]
    | succ n ih =>
      have h1 : 1 ≤ (y n) ^ δ := Real.one_le_rpow (by linarith) hδ
      rw [hstep, Nat.cast_succ]
      linarith
  have hbase (n : ℕ) : x ≤ y n := by
    have := hlin n
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hex : ∃ n : ℕ, z ≤ y n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (z - x)
    exact ⟨n, by linarith [hlin n]⟩
  let K := Nat.find hex
  have hend : z ≤ y K := Nat.find_spec hex
  have hK : 0 < K := by
    by_contra hh
    have hk0 : K = 0 := by omega
    rw [hk0, hy0] at hend
    linarith
  have hprev : y (K - 1) < z := by
    exact lt_of_not_ge (Nat.find_min hex (show K - 1 < K by omega))
  have hlast : y K ≤ z + z ^ δ := by
    have heq : K = K - 1 + 1 := by omega
    rw [heq, hstep]
    have hp : (y (K - 1)) ^ δ ≤ z ^ δ :=
      Real.rpow_le_rpow (by linarith [hbase (K - 1)]) hprev.le hδ
    linarith
  exact ⟨y, K, hK, hy0, hstep, hbase, hend, hlast⟩

/-- Page 2, interval covering detail: For x at least 1 and 0 at most delta at most 1 with delta at most theta, the delta power of x plus x to theta is at most twice x to theta. -/
theorem endpoint_rpow_le {x δ θ : ℝ} (hx : 1 ≤ x) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hδθ : δ ≤ θ) :
    (x + x ^ θ) ^ δ ≤ 2 * x ^ θ := by
  have hx0 : 0 < x := by linarith
  have hθ0 : 0 ≤ θ := le_trans hδ0 hδθ
  have hxmax : x ≤ x ^ (max 1 θ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (le_max_left 1 θ)
  have hpowmax : x ^ θ ≤ x ^ (max 1 θ) :=
    Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 θ)
  have hprod : max 1 θ * δ ≤ θ := by
    rcases le_total θ 1 with h | h
    · simpa [max_eq_left h] using hδθ
    · rw [max_eq_right h]
      nlinarith
  calc
    (x + x ^ θ) ^ δ ≤ (2 * x ^ (max 1 θ)) ^ δ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hδ0
    _ = (2 : ℝ) ^ δ * x ^ (max 1 θ * δ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]
    _ ≤ 2 * x ^ θ := by
      apply mul_le_mul
      · simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hδ1
      · exact Real.rpow_le_rpow_of_exponent_le hx hprod
      · positivity
      · norm_num

/-- Page 2, interval covering detail: The exceptional count on an interval covered by a finite consecutive chain is at most the sum of exceptional counts on its adjacent intervals. -/
theorem exception_cover (y : ℕ → ℝ) {K : ℕ} (hK : 0 < K) {z : ℝ}
    (hz : 0 ≤ z) (hzK : z ≤ y K) :
    exceptions (y 0) (z - y 0) ≤
      ∑ i ∈ Finset.range K, exceptions (y i) (y (i + 1) - y i) := by
  let F : Finset ℕ := (Finset.Icc ⌈y 0⌉₊ ⌊z⌋₊).filter
    (fun n => Even n ∧ ¬ IsGoldbachSum n)
  let G : ℕ → Finset ℕ := fun i => (Finset.Icc ⌈y i⌉₊ ⌊y (i + 1)⌋₊).filter
    (fun n => Even n ∧ ¬ IsGoldbachSum n)
  have hsub : F ⊆ (Finset.range K).biUnion G := by
    intro n hn
    simp only [F, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn0, hnz⟩, hEven, hbad⟩ := hn
    have hnr : (n : ℝ) ≤ z := le_trans (by exact_mod_cast hnz) (Nat.floor_le hz)
    obtain ⟨i, hi, hni, hin⟩ := mesh_cover y hK (Nat.ceil_le.mp hn0) (le_trans hnr hzK)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hni, Nat.le_floor hin⟩, hEven, hbad⟩
  have hcard : F.card ≤ ∑ i ∈ Finset.range K, (G i).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have cancel (a b : ℝ) : a + (b - a) = b := by ring
  simpa only [F, G, exceptions, cancel] using hcard

/-- Page 2, interval covering detail: For the mesh with step y to delta, the sum of the first K step lengths equals the last endpoint minus the first. -/
theorem mesh_sum (y : ℕ → ℝ) (δ : ℝ)
    (hstep : ∀ i, y (i + 1) = y i + (y i) ^ δ) (K : ℕ) :
    ∑ i ∈ Finset.range K, (y i) ^ δ = y K - y 0 := by
  induction K with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, hstep]; ring

end LeanLab.BHP1997.Decomp132
