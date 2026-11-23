import LeanLab.ChenDoubleSieve.Decomp349b

/-!
Split of `Task349.switched_sum_tendsto`, Wu 2004 page 41, equation 10.9 and its
analogue in 10.11. Source: https://arxiv.org/pdf/0705.1652.
The coprimality restriction is removed, the free prime double sum is replaced by
a double integral by prime partial summation, and the double integral is
evaluated in closed form.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The switched prime pairs of `switchedPairs` without the coprimality to N,
Wu 2004 page 41 display 10.9. -/
def freePairs (N : ℕ) (i : Fin 12) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun q => q.1.Prime ∧ q.2.Prime ∧
    (if i = 6 then (N : ℝ) ^ sigma1 ≤ q.1 else
      if i = 7 then (N : ℝ) ^ sigma2 ≤ q.1 else
        (N : ℝ) ^ kappa2 ≤ q.1 ∧ (q.1 : ℝ) < (N : ℝ) ^ sigma2 ∧
          (N : ℝ) ^ sigma2 ≤ q.2) ∧
    q.1 < q.2 ∧ (q.2 : ℝ) < sqrt ((N : ℝ) / q.1))

/-- The switched sum of `switchedSum` over `freePairs`. -/
def freeSum (N : ℕ) (i : Fin 12) : ℝ :=
  ∑ q ∈ freePairs N i,
    1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2)))

/-- The double integral limit of Wu 2004 page 41 before evaluation, in the
variables t equal log p over log N and u equal log q over log N. -/
def switchedIntegral (i : Fin 12) : ℝ :=
  if i = 9 then
    ∫ t in kappa2..sigma2, ∫ u in sigma2..((1 - t) / 2), 1 / (t * u * (1 - t - u))
  else
    ∫ t in (if i = 6 then sigma1 else sigma2)..(1 / 3 : ℝ),
      ∫ u in t..((1 - t) / 2), 1 / (t * u * (1 - t - u))

/-- LEAF: Wu 2004 page 41, removal of the coprimality condition in 10.9: at most
1 over kappa two primes above N to kappa two divide N, so the pairs with p or q
dividing N contribute o of 1 over log N. Class MEDIUM. -/
theorem leaf_coprime_removal :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * (switchedSum N i - freeSum N i)) evenAtTop
        (𝓝 0) := by
  sorry

/-- LEAF: Wu 2004 page 41, display 10.9 and 10.11: prime partial summation with
the prime number theorem replaces the free double prime sum by the double
integral in t and u. Class HARD. -/
theorem leaf_free_sum_tendsto :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * freeSum N i) atTop
        (𝓝 (8 * switchedIntegral i)) := by
  sorry

/-- LEAF: Wu 2004 page 41, evaluation of the double integral: the inner integral is
log of 1 minus 2 t over t, or log of 1 minus t minus sigma two over sigma two,
divided by 1 minus t, and the substitution s equal 1 minus t over t gives the
coefficients of 10.9 and 10.11. Class MEDIUM. -/
theorem leaf_switched_integral_eval :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      8 * switchedIntegral i =
        integralTerms (fun _ => 0) (fun _ => 0) (fun _ => 0) i := by
  sorry

/-- `switched_sum_tendsto`, exactly as stated in `Decomp349b`, proved from the three
leaves above. CONDITIONAL ON the LEAFs. -/
theorem switched_sum_tendsto_of_leaves :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * switchedSum N i) evenAtTop
        (𝓝 (integralTerms (fun _ => 0) (fun _ => 0) (fun _ => 0) i)) := by
  intro i hi
  have h1 := leaf_coprime_removal i hi
  have h2 := tendsto_inf_left (x₂ := principal {N : ℕ | Even N})
    (leaf_free_sum_tendsto i hi)
  have h := h1.add h2
  rw [zero_add, leaf_switched_integral_eval i hi] at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  simp only
  ring

end LeanLab.ChenDoubleSieve.Task349
