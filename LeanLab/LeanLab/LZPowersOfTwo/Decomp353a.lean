/-
P0079 page 4, finite expansion for the counting integral.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, the finite box before display 11, without the inequality filter. -/
def candidates353 (s : ℕ) (μ : ℕ → ℝ) (ε X : ℝ) :
    Finset (ℕ × ℕ × (Fin s → ℕ)) :=
  let P := (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))
  P ×ˢ (P ×ˢ Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊))

/-- P0079 page 4, expansion of the product defining I before display 13.
The integrand is a finite weighted character sum times the kernel. -/
theorem integrand_expansion353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ)
    (γ η ε X α : ℝ) :
    integrand293 s l1 l2 μ γ η ε X α =
      (∑ x ∈ candidates353 s μ ε X,
        ((log x.1 * log x.2.1 : ℝ) : ℂ) *
          character293 (form l1 l2 (fun i : Fin s => μ i) γ x.1 x.2.1 x.2.2 * α)) *
        (kernel293 η α : ℂ) := by
  classical
  unfold integrand293 primeSum293 powerSum293
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.prod_univ_sum]
  simp only [candidates353, Finset.sum_product]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro m hm
  rw [← character_sum293]
  simp only [form, add_mul, Finset.sum_mul, character_add293]
  push_cast
  ring

/-- P0079 page 4, displays 11 to 13. The exact counting target follows from
finite expansion, the proved kernel transform and the weighted counting bound. -/
theorem count_integral353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hX : 2 ≤ X) :
    Integrable (integrand293 s l1 l2 μ γ η ε X) ∧
    (∫ α : ℝ, integrand293 s l1 l2 μ γ η ε X α).re ≤
      η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  classical
  refine ⟨integrand_integrable293 s l1 l2 μ γ η ε X, ?_⟩
  have hi := finite_kernel_integral293 (candidates353 s μ ε X)
    (fun x => ((log x.1 * log x.2.1 : ℝ) : ℂ))
    (fun x => form l1 l2 (fun i : Fin s => μ i) γ x.1 x.2.1 x.2.2) η hη
  have heq : (∫ α : ℝ, integrand293 s l1 l2 μ γ η ε X α).re =
      ∑ x ∈ candidates353 s μ ε X, log x.1 * log x.2.1 *
        max 0 (η - |form l1 l2 (fun i : Fin s => μ i) γ x.1 x.2.1 x.2.2|) := by
    simp_rw [integrand_expansion353]
    rw [hi]
    simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [heq]
  apply weighted_count_le293 l1 l2 (fun i : Fin s => μ i) γ η ε X hη hX
  intro x hx
  simp only [candidates353, mem_product, mem_filter, mem_range,
    Fintype.mem_piFinset, mem_Icc] at hx
  refine ⟨hx.1.2.1, hx.2.1.2.1, fun i => (hx.2.2 i).1, hx.1.2.2, ?_,
    hx.2.1.2.2, ?_, ?_⟩
  · exact (by exact_mod_cast Nat.le_of_lt_succ hx.1.1 : (x.1 : ℝ) ≤ ⌊X⌋₊).trans
      (Nat.floor_le (by linarith))
  · exact (by exact_mod_cast Nat.le_of_lt_succ hx.2.1.1 : (x.2.1 : ℝ) ≤ ⌊X⌋₊).trans
      (Nat.floor_le (by linarith))
  · intro i
    have hL : 0 < cutoff293 s μ ε X := Nat.pos_of_floor_pos
      (lt_of_lt_of_le Nat.zero_lt_one ((hx.2.2 i).1.trans (hx.2.2 i).2))
    exact (by exact_mod_cast (hx.2.2 i).2 :
      (x.2.2 i : ℝ) ≤ ⌊cutoff293 s μ ε X⌋₊).trans (Nat.floor_le hL.le)

end LeanLab.LZPowersOfTwo
