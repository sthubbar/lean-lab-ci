/-
P0070, estimate 7 on p. 359, through equation 27 on p. 364.
This is a coarse decomposition. The two analytic blocks remain open.
The final assembly contains no sorry but depends on those open leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Statements

namespace LeanLab.PerelliPintz1992.Decomp97
open Real ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The parameter Q on p. 357. -/
def Q (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 2 : ℝ) / 2

/-- The short interval parameter on p. 358. -/
def H (N : ℕ) (ε : ℝ) : ℝ := (N : ℝ) ^ (1 / 2 + ε)

/-- The actual W on p. 364, with the lab's inclusive sum convention. -/
def W (N : ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) : ℝ :=
  Real.sqrt ((1 / (((q : ℝ) * Q N) ^ 2 * N)) *
    ∫ x in Ioc ((N : ℝ) / 2) (2 * N : ℝ),
      ‖∑ n ∈ (Finset.Icc N (2 * N)).filter
          (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + 2 * q * Q N),
        ((Λ n : ℂ) * χ (n : ZMod (q : ℕ)) - if χ = 1 then 1 else 0)‖ ^ 2)

/-- The modulus family on p. 363, using enclosing symmetric Farey arcs. -/
def Y (N : ℕ) (ε ξ : ℝ) (M : ℕ) : Finset ℕ+ :=
  ((Finset.Icc 1 ⌊Q N⌋₊).attach.image
    (fun q => (⟨q.val, (Finset.mem_Icc.mp q.property).1⟩ : ℕ+))).filter
      (fun q => M ≤ (q : ℕ) ∧ (q : ℕ) ≤ 2 * M ∧
        ∃ a ∈ Finset.Icc 1 (q : ℕ), Nat.Coprime a (q : ℕ) ∧ ∃ α : ℝ,
          |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q N) ∧ |α - ξ| < 1 / H N ε)

/-- The character expression inside the supremum in 27 on p. 364. -/
def energy (N : ℕ) (ε ξ : ℝ) (M : ℕ) : ℝ :=
  (1 / (M : ℝ) ^ 2) * ∑ q ∈ Y N ε ξ M,
    ∑ χ₁ : DirichletCharacter ℂ (q : ℕ), ∑ χ₂ : DirichletCharacter ℂ (q : ℕ),
      ‖gaussSum χ₁ ZMod.stdAddChar * gaussSum χ₂ ZMod.stdAddChar‖ * W N χ₁ * W N χ₂

/-- LEAF. Equation 27, p. 364: the double character expression is the square
of the Gauss weighted W sum at each modulus. -/
theorem energy_eq_square (N : ℕ) (ε ξ : ℝ) (M : ℕ) :
    energy N ε ξ M = (1 / (M : ℝ) ^ 2) * ∑ q ∈ Y N ε ξ M,
      (∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * W N χ) ^ 2 := by
  unfold energy
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [norm_mul]
  ring

attribute [-instance] Finset.decidableExistsAndFinsetCoe Finset.decidableExistsAndFinset in
/-- Increasing epsilon shrinks the actual Farey window family on p. 363. -/
theorem Y_subset_epsilon {N : ℕ} (hN : 1 ≤ N) {ε ε' : ℝ} (hε : ε ≤ ε') (ξ : ℝ) (M : ℕ) :
    Y N ε' ξ M ⊆ Y N ε ξ M := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH : H N ε ≤ H N ε' := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN) (by linarith)
  have hw : 1 / H N ε' ≤ 1 / H N ε := one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos hNp _) hH
  intro q hq
  obtain ⟨hb, hM, hM', a, ha, hc, α, hα, hx⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hb, hM, hM', a, ha, hc, α, hα, hx.trans_le hw⟩

/-- The actual energy in 27 decreases when the window shrinks. This permits the
sufficiently small epsilon argument to be extended to larger positive epsilon. -/
theorem energy_antitone_epsilon {N : ℕ} (hN : 1 ≤ N) {ε ε' : ℝ} (hε : ε ≤ ε')
    (ξ : ℝ) (M : ℕ) : energy N ε' ξ M ≤ energy N ε ξ M := by
  unfold energy
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Y_subset_epsilon hN hε ξ M)
  intro q hq hq'
  apply Finset.sum_nonneg
  intro χ hχ
  apply Finset.sum_nonneg
  intro ψ hψ
  apply mul_nonneg
  · exact mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  · exact Real.sqrt_nonneg _

/-- LEAF. Equation 27, p. 364, with the supremum replaced by an upper bound E.
The missing proof includes the Farey split, the character expansion and Gallagher's lemma,
P. X. Gallagher, Invent. Math. 11, 1970, pp. 329 to 339. -/
theorem reduction27 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ,
        0 ≤ ξ → ξ ≤ 1 → ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energy N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  sorry

/-- LEAF. Sections 5 and 6, pp. 365 to 372: the character expression in 27
has every logarithmic saving. The missing proof includes 28 and 31 to 55.
Outside inputs are Davenport Ch. 19, Saffari and Vaughan Lemmas 5 and 6,
Montgomery Ch. 12, and Prachar Ch. 8 with the lower Siegel gap needed on p. 372.
The open sign question in ZeroFreeInputs remains separate. -/
theorem energy_decay :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 12 → ∀ D : ℝ, 0 < D →
      ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
        ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energy N ε ξ M ≤ C * L N ^ (-D) := by
  sorry

/-- The exact existing Estimate7 Prop, assembled from the two open analytic leaves.
CONDITIONAL ON reduction27 and energy_decay. This does not prove either leaf. -/
theorem estimate7 : Estimate7 := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27
  refine ⟨min ε₁ (1 / 12), lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hεsmall A hA
  have hεred : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεden : ε < 1 / 12 := lt_of_lt_of_le hεsmall (min_le_right _ _)
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ := hred ε hε hεred A hA
  obtain ⟨K, N₁, hK, hdecay⟩ := energy_decay ε hε hεden (A + 1 + c) (by linarith)
  refine ⟨C * (K + 1), max (max N₀ N₁) 2, ?_⟩
  intro N hN ξ hξ hξ'
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂ : 2 ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN : (2 : ℝ) ≤ N)
  have hL := L_pos hN₂
  have he := hbound N hN₀ ξ hξ hξ' (K * L N ^ (-(A + 1 + c)))
    (by positivity) (hdecay N hN₁ ξ hξ hξ')
  have hprod : L N ^ c * (K * L N ^ (-(A + 1 + c))) = K * L N ^ (-(A + 1)) := by
    calc
      _ = K * (L N ^ c * L N ^ (-(A + 1 + c))) := by ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  change (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
    ‖S N α‖ ^ 2) ≤ _
  calc
    _ ≤ C * N * (L N ^ c * (K * L N ^ (-(A + 1 + c))) + L N ^ (-(A + 1))) := he
    _ = (C * (K + 1)) * N / L N ^ (A + 1) := by
      rw [hprod, Real.rpow_neg hL.le]
      ring

end
end LeanLab.PerelliPintz1992.Decomp97
