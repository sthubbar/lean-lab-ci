import LeanLab.ChenDoubleSieve.Decomp348d

/-!
Uniform elementary coprimality error for Wu 2004 equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39, display after equation 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275

/-- The power cutoff gives the coprimality error with only one logarithm. -/
theorem badPairs_mass_sharp (P Q : Finset ℕ) {N : ℕ} (hN : 2 ≤ N)
    {κ : ℝ} (hκ : 0 < κ)
    (hP : ∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ κ ≤ p ∧ p ≤ N)
    (hQ : ∀ q ∈ Q, q.Prime ∧ (N : ℝ) ^ κ ≤ q ∧ q ≤ N) :
    pairMass (badPairs N P Q) ≤ 2 / (κ * (N : ℝ) ^ κ) * (1 + log N) := by
  have hbadP := exceptional_reciprocal_sum_sharp P hN hκ (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
  have hbadQ := exceptional_reciprocal_sum_sharp Q hN hκ (fun q hq => ⟨(hQ q hq).1, (hQ q hq).2.1⟩)
  have hsumP := reciprocal_sum_le P N (fun p hp => ⟨(hP p hp).1.one_le, (hP p hp).2.2⟩)
  have hsumQ := reciprocal_sum_le Q N (fun q hq => ⟨(hQ q hq).1.one_le, (hQ q hq).2.2⟩)
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hmain : 0 ≤ 1 / (κ * (N : ℝ) ^ κ) := by positivity
  rw [badPairs_eq]
  calc
    _ ≤ pairMass (P.filter (fun p => ¬ p.Coprime N) ×ˢ Q) +
        pairMass (P ×ˢ Q.filter (fun q => ¬ q.Coprime N)) := by
      let A := P.filter (fun p => ¬ p.Coprime N) ×ˢ Q
      let C := P ×ˢ Q.filter (fun q => ¬ q.Coprime N)
      have he := Finset.sum_union_inter (s₁ := A) (s₂ := C)
        (f := fun q : ℕ × ℕ => 1 / ((q.1 : ℝ) * q.2))
      have hp : 0 ≤ pairMass (A ∩ C) := sum_nonneg (by intros; positivity)
      change pairMass (A ∪ C) ≤ pairMass A + pairMass C
      change pairMass (A ∪ C) + pairMass (A ∩ C) = pairMass A + pairMass C at he
      linarith
    _ = (∑ p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / (p : ℝ)) *
          (∑ q ∈ Q, 1 / (q : ℝ)) +
        (∑ p ∈ P, 1 / (p : ℝ)) *
          (∑ q ∈ Q.filter (fun q => ¬ q.Coprime N), 1 / (q : ℝ)) := by
      rw [pairMass_product, pairMass_product]
    _ ≤ (1 / (κ * (N : ℝ) ^ κ)) * (1 + log N) +
        (1 + log N) * (1 / (κ * (N : ℝ) ^ κ)) := by
      apply add_le_add
      · exact mul_le_mul hbadP hsumQ (sum_nonneg (by intros; positivity)) hmain
      · exact mul_le_mul hsumP hbadQ (sum_nonneg (by intros; positivity)) (by linarith)
    _ = _ := by ring

/-- The sharp elementary error tends to zero at every positive power cutoff. -/
theorem coprimality_bound_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => 2 / (κ * x ^ κ) * (1 + log x)) atTop (𝓝 0) := by
  have hzero : Tendsto (fun x : ℝ => 1 / x ^ κ) atTop (𝓝 0) := by
    simpa only [rpow_zero] using
      (isLittleO_log_rpow_rpow_atTop (0 : ℝ) hκ).tendsto_div_nhds_zero
  have hone : Tendsto (fun x : ℝ => log x / x ^ κ) atTop (𝓝 0) := by
    simpa only [rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hκ).tendsto_div_nhds_zero
  have ht := (hzero.add hone).const_mul (2 / κ)
  convert ht using 1
  · ext x
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · simp

/-- The bad pair reciprocal mass tends uniformly to zero over all allowed domains. -/
theorem badPairs_mass_small {κ : ℝ} (hκ : 0 < κ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ P Q : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ κ ≤ p ∧ p ≤ N) →
      (∀ q ∈ Q, q.Prime ∧ (N : ℝ) ^ κ ≤ q ∧ q ≤ N) →
      pairMass (badPairs N P Q) ≤ ε := by
  have he : ∀ᶠ N : ℕ in atTop, 2 / (κ * (N : ℝ) ^ κ) * (1 + log N) < ε :=
    (coprimality_bound_tendsto hκ).comp tendsto_natCast_atTop_atTop |>.eventually
      (eventually_lt_nhds hε)
  obtain ⟨M, hM⟩ := eventually_atTop.1 he
  refine ⟨max 2 M, ?_⟩
  intro N hN P Q hP hQ
  exact (badPairs_mass_sharp P Q (by omega) hκ hP hQ).trans (hM N (by omega)).le

/-- Multiplication by N gives the paper's power times logarithm error. -/
theorem badPairs_count_error (P Q : Finset ℕ) {N : ℕ} (hN : 2 ≤ N)
    {κ : ℝ} (hκ : 0 < κ)
    (hP : ∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ κ ≤ p ∧ p ≤ N)
    (hQ : ∀ q ∈ Q, q.Prime ∧ (N : ℝ) ^ κ ≤ q ∧ q ≤ N) :
    (N : ℝ) * pairMass (badPairs N P Q) ≤
      (2 / κ) * (N : ℝ) ^ (1 - κ) * (1 + log N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he := mul_le_mul_of_nonneg_left (badPairs_mass_sharp P Q hN hκ hP hQ) hpos.le
  calc
    _ ≤ (N : ℝ) * (2 / (κ * (N : ℝ) ^ κ) * (1 + log N)) := he
    _ = _ := by
      rw [rpow_sub hpos, rpow_one]
      simp only [div_eq_mul_inv, mul_inv]
      ring

end LeanLab.ChenDoubleSieve.Task348
