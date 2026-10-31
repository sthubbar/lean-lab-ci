/-
P0083 Perelli 1996, page 482 equation 9.
The Weyl decay exponent under the rational denominator exclusions.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp88
import LeanLab.Perelli1996.Farey103

namespace LeanLab.Perelli1996.Section2
open Finset Real Polynomial
noncomputable section

/-- Equation 9 from the Weyl input and the three explicit denominator exclusions.
CONDITIONAL ON the stated Weyl input. -/
theorem weyl_decay_of_denominator_bounds (F : ℤ[X]) (hF : Admissible F)
    (hW : WeylLemma F) (B : ℝ)
    (hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ a : ℤ, ∀ q : ℕ, 0 < q → Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      1 / (q : ℝ) ≤ Real.log N ^ (-B / 4) →
      1 / H ≤ Real.log N ^ (-B / 4) →
      (q : ℝ) / H ^ F.natDegree ≤ Real.log N ^ (-B / 4) →
      ‖polynomialKernel F N H α‖ ≤ C * H *
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * weylExponent F)) := by
  let D := B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1
  let K := weylExponent F
  have hK : 0 < K := by dsimp [K, weylExponent]; positivity
  obtain ⟨C, N₀, hC, hN₀, hw⟩ := hW hF D hD
  refine ⟨C * 4 ^ (1 / K), N₀, by positivity, hN₀, ?_⟩
  intro N H α hN hH hHu a q hq hcop happ h1 h2 h3
  have hN3 := hN₀.trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hw' := hw N H α hN hH hHu a q hq hcop happ
  have hfour : -2 * D + (F.natDegree : ℝ) ^ 2 - 2 = -B / 4 := by dsimp [D]; ring
  rw [hfour] at hw'
  have hbase : 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
      Real.log N ^ (-B / 4) ≤ 4 * Real.log N ^ (-B / 4) := by linarith
  have hnon : 0 ≤ 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
      Real.log N ^ (-B / 4) := by positivity
  have hroot := Real.rpow_le_rpow hnon hbase (show 0 ≤ 1 / K by positivity)
  calc
    _ ≤ C * H * (4 * Real.log N ^ (-B / 4)) ^ (1 / K) *
      Real.log N ^ ((D + 1) / K) := by
      exact hw'.trans (by gcongr)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hL.le _),
        ← Real.rpow_mul hL.le]
      have hexp : (-B / 4) * (1 / K) + (D + 1) / K =
          -(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * K) := by dsimp [D]; ring
      calc
        _ = (C * 4 ^ (1 / K)) * H *
            (Real.log N ^ ((-B / 4) * (1 / K)) * Real.log N ^ ((D + 1) / K)) := by ring
        _ = _ := by rw [← Real.rpow_add hL, hexp]

/-- The small B range has a nondecaying equation 9 exponent. -/
theorem weyl_decay_exponent_nonneg (F : ℤ[X]) (B : ℝ)
    (hB : B ≤ 4 * (F.natDegree : ℝ) ^ 2) :
    0 ≤ -(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * weylExponent F) := by
  apply div_nonneg (by linarith)
  unfold weylExponent
  positivity
/-- The reciprocal interval length satisfies the secondary minor arc threshold for large N. -/
theorem reciprocal_H_le_log (F : ℤ[X]) (hF : Admissible F) (ε B : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      1 / H ≤ Real.log N ^ (-B / 4) := by
  let δ := 1 / (3 * (F.natDegree : ℝ)) + ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb := (isLittleO_log_rpow_rpow_atTop (B / 4) hδ).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hlog := hN₁ N ((le_max_right _ _).trans hN)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] at hlog
  have hlogH : Real.log N ^ (B / 4) ≤ H := hlog.trans hH
  rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hL.le]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _) hlogH

/-- Equation 9 on the complement of the secondary rational arcs.
CONDITIONAL ON Weyl. The rational approximation and denominator exclusions are proved. -/
theorem weyl_decay_secondary_minor (F : ℤ[X]) (hF : Admissible F)
    (hW : WeylLemma F) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B)
    (hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B / 4) →
        ∀ a : ℤ, Nat.Coprime a.natAbs q →
          1 / ((q : ℝ) * (H ^ F.natDegree * Real.log N ^ (-B / 4))) <
            |α - (a : ℝ) / q|) →
      ‖polynomialKernel F N H α‖ ≤ C * H *
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * weylExponent F)) := by
  obtain ⟨C, NW, hC, hNW, hw⟩ := weyl_decay_of_denominator_bounds F hF hW B hD
  obtain ⟨NH, hNH, hh⟩ := reciprocal_H_le_log F hF ε B hε
  obtain ⟨NG, hNG, hg⟩ := Decomp88.arc_parameters F hF ε B hε hB
  refine ⟨C, max NW (max NH NG), hC, hNW.trans (le_max_left _ _), ?_⟩
  intro N H α hN hH hHu hminor
  have hNW' := (le_max_left NW (max NH NG)).trans hN
  have hNH' := (le_max_left NH NG).trans ((le_max_right NW (max NH NG)).trans hN)
  have hNG' := (le_max_right NH NG).trans ((le_max_right NW (max NH NG)).trans hN)
  have hN3 := hNW.trans hNW'
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  let Q := H ^ F.natDegree * Real.log N ^ (-B / 4)
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have hQ1 : 1 ≤ Q := by
    have hroot := (hg N H hNG' hH).2
    change 2 ≤ Real.sqrt Q / 2 at hroot
    have hs := Real.sq_sqrt hQ0.le
    nlinarith [Real.sqrt_nonneg Q]
  obtain ⟨q, hq, hqQ, a, hcop, happ⟩ := Farey103.dirichlet_real_order α Q hQ1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmall : ¬ (q : ℝ) ≤ Real.log N ^ (B / 4) := by
    intro hbad
    exact (not_lt_of_ge happ.le) (hminor q hq hbad a hcop)
  have hqLarge : Real.log N ^ (B / 4) ≤ q := (lt_of_not_ge hsmall).le
  have happ' : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.le.trans ?_
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq0)
    nlinarith
  apply hw N H α hNW' hH1 hHu a q hq hcop happ'
  · rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hL.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _) hqLarge
  · exact hh N H hNH' hH
  · exact (div_le_iff₀ (pow_pos hH0 _)).mpr (by simpa [Q, mul_comm] using hqQ)


end
end LeanLab.Perelli1996.Section2
