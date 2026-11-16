import LeanLab.ChenDoubleSieve.Task587PolynomialTools

/-!
Exact box moments for Wu 2004 Lemma 5.2 page 26, D2,13.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Separated coordinate intervals make the ordering condition automatic.
Wu 2004 page 26, derived geometry of D2,13. -/
theorem domain_eq_box_of_separated {n : ℕ} (lo hi : Fin n → ℝ)
    (hsep : ∀ i j, i < j → hi i ≤ lo j) : domain lo hi = Set.Icc lo hi := by
  ext x
  constructor
  · intro hx
    exact ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩
  · intro hx
    refine ⟨?_, fun j => ⟨hx.1 j, hx.2 j⟩⟩
    intro i j hij
    by_cases he : i = j
    · simpa [he]
    · exact (hx.2 i).trans ((hsep i j (lt_of_le_of_ne hij he)).trans (hx.1 j))

/-- The exact shifted monomial box integral is the product of scalar moments.
Wu 2004 page 26, derived D2,13 polynomial quadrature. -/
theorem box_shifted_monomial (n : ℕ) (k : Fin n → ℕ) (lo hi : Fin n → ℝ)
    (hle : ∀ j, lo j ≤ hi j) :
    (∫ x in Set.Icc lo hi, ∏ j, (x j - lo j) ^ k j) =
      ∏ j, (hi j - lo j) ^ (k j + 1) / (k j + 1) := by
  rw [← pi_univ_Icc]
  change (∫ x, ∏ j, (x j - lo j) ^ k j ∂(Measure.pi (fun _ : Fin n => volume)).restrict
    (Set.univ.pi (fun j : Fin n => Set.Icc (lo j) (hi j)))) = _
  rw [Measure.restrict_pi_pi]
  rw [integral_fin_nat_prod_eq_prod (fun j (x : ℝ) => (x - lo j) ^ k j)]
  apply prod_congr rfl
  intro j _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hle j),
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ k j) (lo j), integral_pow]
  simp only [sub_self, zero_pow (Nat.succ_ne_zero _), sub_zero]

/-- Exact rational coefficient moments on a box with coordinate-specific endpoints.
Wu 2004 page 26, derived finite certificate arithmetic. -/
def listMomentBox {n : ℕ} (ts : List (ℚ × (Fin n → ℕ))) (lo hi : Fin n → ℚ) : ℚ :=
  (ts.map fun t => t.1 * ∏ j, (hi j - lo j) ^ (t.2 j + 1) / (t.2 j + 1)).sum

/-- The shifted coefficient polynomial integral equals its exact rational box moment.
Wu 2004 page 26, derived D2,13 quadrature theorem. -/
theorem integral_listEvalBox {n : ℕ} (ts : List (ℚ × (Fin n → ℕ))) (lo hi : Fin n → ℚ)
    (hle : ∀ j, lo j ≤ hi j) :
    (∫ x in Set.Icc (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
      listEvalN ts (fun j => x j - (lo j : ℝ))) = (listMomentBox ts lo hi : ℝ) := by
  have hle' (j : Fin n) : (lo j : ℝ) ≤ (hi j : ℝ) := by exact_mod_cast hle j
  induction ts with
  | nil => simp [listEvalN, listMomentBox]
  | cons t ts ih =>
    have ht : IntegrableOn (fun x : Fin n → ℝ =>
        (t.1 : ℝ) * ∏ j, (x j - (lo j : ℝ)) ^ t.2 j)
        (Set.Icc (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) volume := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      fun_prop
    have hs : IntegrableOn (fun x : Fin n → ℝ => listEvalN ts (fun j => x j - (lo j : ℝ)))
        (Set.Icc (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) volume := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact ((listEvalN_continuous ts).comp (by fun_prop)).continuousOn
    change (∫ x in Set.Icc (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
      (t.1 : ℝ) * (∏ j, (x j - (lo j : ℝ)) ^ t.2 j) +
        listEvalN ts (fun j => x j - (lo j : ℝ))) = _
    rw [MeasureTheory.integral_add ht hs, MeasureTheory.integral_const_mul,
      box_shifted_monomial n t.2 _ _ hle', ih]
    simp only [listMomentBox, List.map_cons, List.sum_cons]
    push_cast
    ring

end LeanLab.ChenDoubleSieve.Task587
