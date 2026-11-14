/-
A finer split of the real interval minor arc transference in P0088 pages 7 and 8.
The weighted Dirichlet kernel estimate and the local quadratic mass estimate
are independent smaller analytic tasks. Their combination is proved below.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a
import LeanLab.PNTPort.Gallagher.Basic

namespace LeanLab.KumchevLiu2007.Task556d

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 4 display 13, the rough quadratic exponential sum S2. -/
noncomputable def roughSum (Y P α : ℝ) : ℂ :=
  ∑ m ∈ squareWindow Y, roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m *
    fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))

/-- Page 4 display 13, the prime exponential sum S1. -/
noncomputable def primeSum (X Y α : ℝ) : ℂ :=
  ∑ m ∈ (primeWindow X Y).filter Nat.Prime, fourier (m : ℤ) (α : AddCircle (1 : ℝ))

/-- The page 15 prime and rough pair support is a Cartesian product. -/
theorem roughPairs_eq_product (X Y P : ℝ) :
    roughPairs X Y P = ((primeWindow X Y).filter Nat.Prime).product
      ((squareWindow Y).filter (fun m => ∀ p : ℕ, p.Prime → p ∣ m →
        Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))) := by
  ext v
  simp only [roughPairs, primeWindow, squareWindow, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  tauto

/-- Page 4 display 10 converts the rough indicator sum into a filtered sum. -/
theorem roughSum_eq_filtered_sum (Y P α : ℝ) :
    roughSum Y P α = ∑ m ∈ (squareWindow Y).filter
      (fun m => ∀ p : ℕ, p.Prime → p ∣ m →
        Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ)),
      fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  simp [roughSum, roughWeight, Finset.sum_filter, ite_mul]

/-- Page 4 display 13: the representation polynomial factors as S1 times S2. -/
theorem representationPolynomial_eq_prime_mul_rough (X Y P α : ℝ) :
    representationPolynomial X Y P (α : AddCircle (1 : ℝ)) = primeSum X Y α * roughSum Y P α := by
  rw [representationPolynomial, roughPairs_eq_product, Finset.product_eq_sprod, Finset.sum_product,
    primeSum, roughSum_eq_filtered_sum, Finset.sum_mul_sum]
  simp only [Nat.cast_add, fourier_add]

/-- The cancellation free prime exponential sum estimate. -/
theorem primeSum_norm_le_card (X Y α : ℝ) : ‖primeSum X Y α‖ ≤ (primeWindow X Y).card := by
  unfold primeSum
  calc
    _ ≤ ∑ m ∈ (primeWindow X Y).filter Nat.Prime,
        ‖fourier (m : ℤ) (α : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
    _ = (((primeWindow X Y).filter Nat.Prime).card : ℝ) := by simp only [fourier_apply, Circle.norm_coe, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (primeWindow X Y).card := by exact_mod_cast Finset.card_filter_le (primeWindow X Y) Nat.Prime

/-- The cancellation free rough quadratic sum estimate. -/
theorem roughSum_norm_le_card (Y P α : ℝ) : ‖roughSum Y P α‖ ≤ (squareWindow Y).card := by
  rw [roughSum_eq_filtered_sum]
  calc
    _ ≤ ∑ m ∈ (squareWindow Y).filter
        (fun m => ∀ p : ℕ, p.Prime → p ∣ m → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ)),
        ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
    _ = (((squareWindow Y).filter
        (fun m => ∀ p : ℕ, p.Prime → p ∣ m → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) := by
      simp only [fourier_apply, Circle.norm_coe, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (squareWindow Y).card := by exact_mod_cast Finset.card_filter_le (squareWindow Y) _

/-- The circle Fourier monomial is the lab exponential e at a natural frequency. -/
theorem fourier_nat_eq_e (n : ℕ) (α : ℝ) :
    fourier (n : ℤ) (α : AddCircle (1 : ℝ)) = LeanLab.PNTPort.LargeSieve.e (n * α) := by
  rw [fourier_coe_apply]
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- Page 5 display 17, finite Parseval for the prime exponential sum on a centered period. -/
theorem primeSum_parseval_centered (X Y : ℝ) :
    (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖primeSum X Y α‖ ^ 2) =
      (((primeWindow X Y).filter Nat.Prime).card : ℝ) := by
  let S := (primeWindow X Y).filter Nat.Prime
  let N := ⌊X⌋₊ + 1
  let a : ℕ → ℂ := fun m => if m ∈ S then 1 else 0
  have hsub : S ⊆ Finset.range N := by
    intro m hm
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
  have hfilter : (Finset.range N).filter (fun m => m ∈ S) = S := by
    ext m
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hs : ∀ α : ℝ, primeSum X Y α =
      ∑ m ∈ Finset.range N, a m * LeanLab.PNTPort.LargeSieve.e (m * α) := by
    intro α
    change (∑ m ∈ S, fourier (m : ℤ) (α : AddCircle (1 : ℝ))) = _
    simp_rw [fourier_nat_eq_e]
    rw [← hfilter, Finset.sum_filter]
    simp only [a, ite_mul, one_mul, zero_mul]
  have ha : (∑ m ∈ Finset.range N, ‖a m‖ ^ 2) = (S.card : ℝ) := by
    calc
      _ = ∑ m ∈ Finset.range N, if m ∈ S then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        by_cases h : m ∈ S <;> simp [a, h]
      _ = _ := by rw [← Finset.sum_filter, hfilter]; simp
  have hp := LeanLab.PNTPort.Gallagher.parseval a N
  simp_rw [← hs] at hp
  rw [ha] at hp
  exact hp

/-- Page 5 display 17 on the paper unit period. -/
theorem primeSum_parseval (X Y : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖primeSum X Y α‖ ^ 2) =
      (((primeWindow X Y).filter Nat.Prime).card : ℝ) := by
  have hp : Function.Periodic (fun α : ℝ => ‖primeSum X Y α‖ ^ 2) 1 := by
    intro α
    simp only [primeSum, AddCircle.coe_add_period]
  have hi := hp.intervalIntegral_add_eq (0 : ℝ) (-(1 / 2 : ℝ))
  norm_num at hi
  exact hi.trans (primeSum_parseval_centered X Y)

/-- Page 2 display 5, exact ceiling endpoints for the first half open window. -/
theorem primeWindow_eq_Ico (X Y : ℝ) :
    primeWindow X Y = Finset.Ico ⌈X - Y⌉₊ ⌈X⌉₊ := by
  ext m
  simp only [primeWindow, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
    Nat.ceil_le, Nat.lt_ceil]
  constructor
  · rintro ⟨hr, hl, hu⟩
    exact ⟨hl, hu⟩
  · rintro ⟨hl, hu⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hu.le), hl, hu⟩

/-- The prime window of real length at least one contains at most twice that length. -/
theorem primeWindow_card_le {X Y : ℝ} (hXY : 0 ≤ X - Y) (hY : 1 ≤ Y) :
    ((primeWindow X Y).card : ℝ) ≤ 2 * Y := by
  rw [primeWindow_eq_Ico, Nat.card_Ico,
    Nat.cast_sub (Nat.ceil_mono (by linarith : X - Y ≤ X))]
  have hu := Nat.ceil_lt_add_one (by linarith : 0 ≤ X)
  have hl := Nat.le_ceil (X - Y)
  linarith

/-- Page 5 display 17, the clean prime Parseval size bound used in display 29. -/
theorem primeSum_parseval_le {X Y : ℝ} (hXY : 0 ≤ X - Y) (hY : 1 ≤ Y) :
    (∫ α in (0 : ℝ)..1, ‖primeSum X Y α‖ ^ 2) ≤ 2 * Y := by
  rw [primeSum_parseval]
  calc
    _ ≤ ((primeWindow X Y).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (primeWindow X Y) Nat.Prime
    _ ≤ _ := primeWindow_card_le hXY hY

/-- Page 7 display 29. For positive H this equals min of H and inverse circle
distance away from zero distance, and equals H at zero distance. -/
noncomputable def shortKernel (H α β : ℝ) : ℝ :=
  (max H⁻¹ (dist (α : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ))))⁻¹

/-- Page 7 display 29, the minor quadratic mass weighted by the short kernel. -/
noncomputable def kernelMass (Y H P β : ℝ) : ℝ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ,
    ‖roughSum Y P α‖ ^ 2 * shortKernel H α β

/-- The page 7 short kernel is nonnegative for positive H. -/
theorem shortKernel_nonneg {H : ℝ} (hH : 0 < H) (α β : ℝ) :
    0 ≤ shortKernel H α β := by
  unfold shortKernel
  exact inv_nonneg.mpr ((inv_pos.mpr hH).le.trans (le_max_left _ _))

/-- The short kernel is bounded by H, including at zero circle distance. -/
theorem shortKernel_le {H : ℝ} (hH : 0 < H) (α β : ℝ) :
    shortKernel H α β ≤ H := by
  unfold shortKernel
  have h := one_div_le_one_div_of_le (inv_pos.mpr hH)
    (le_max_left H⁻¹ (dist (α : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ))))
  simpa only [one_div, inv_inv] using h

/-- LEAF. P0088 page 7 display 29 with I1 bounded by a constant times Y.
This is the short Dirichlet kernel and Cauchy step. It has no logarithmic
saving hypothesis and no short interval character input. The bound M is
any nonnegative uniform majorant for the weighted quadratic minor mass. -/
theorem minor_mean_square_of_kernel (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ K X0 : ℝ, 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ β ∈ Set.Icc (0 : ℝ) 1,
        kernelMass (windowY X ε) H (Real.log X ^ B) β ≤ M) →
      (∑ n ∈ intervalNumbers X H,
        ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
          K * windowY X ε * M := by
  sorry

/-- LEAF. P0088 page 8 displays 30 and 31 and Gallagher's lemma applied
to the explicit rough A2.3 input. Only the local quadratic mass is bounded.
There is no representation count and no mean square over n in this leaf. -/
theorem kernel_mass_of_A23 (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε)
    (hinput : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in windowY X ε / 4..windowY X ε,
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ β ∈ Set.Icc (0 : ℝ) 1,
        kernelMass (windowY X ε) H (Real.log X ^ B) β ≤ C * H / Real.log X ^ A := by
  sorry

/-- Exact minor transference statement from the two smaller kernel tasks.
CONDITIONAL ON the weighted Fourier and local Gallagher leaves. -/
theorem minor_arc_transference_from_kernel (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε)
    (hinput : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in windowY X ε / 4..windowY X ε,
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      (∑ n ∈ intervalNumbers X H,
        ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
  obtain ⟨K, Xk, hK, hXk, hfourier⟩ := minor_mean_square_of_kernel B ε hB hε
  obtain ⟨C, Xc, hC, hXc, hmass⟩ := kernel_mass_of_A23 A B ε hA hB hε hinput
  refine ⟨K * C, max Xk Xc, mul_pos hK hC, hXk.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have hX2 : 2 ≤ X := hXk.trans ((le_max_left _ _).trans hX)
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos (by linarith : 0 < X) _).trans_le hH
  have hm : 0 ≤ C * H / Real.log X ^ A := by positivity
  have hs := hfourier X H ((le_max_left _ _).trans hX) hH hHX
    (C * H / Real.log X ^ A) hm (hmass X H ((le_max_right _ _).trans hX) hH hHX)
  calc
    _ ≤ _ := hs
    _ = _ := by ring

end LeanLab.KumchevLiu2007.Task556d
