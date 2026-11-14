/-
P0070 page 361, display 16, the uniform ambient cutoff form of Siegel and Walfisz.
This module converts the existing PNTPort theorem to the exact natural cutoff input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Statements
import LeanLab.PNTPort.PsiChi.SiegelWalfisz

namespace LeanLab.PerelliPintz1992.Decomp544b
open Real ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

/-- Page 361, the elementary small cutoff bound used to make display 16 uniform. -/
theorem psi_bounds {Y x : ℕ} (hY : 2 ≤ Y) (hx : x ≤ Y) (q b : ℕ) :
    0 ≤ LeanLab.HeathBrown1985.psi x q b ∧ LeanLab.HeathBrown1985.psi x q b ≤ x * L Y := by
  classical
  have hlog : 0 ≤ L Y := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
  unfold LeanLab.HeathBrown1985.psi
  simp only [Nat.floor_natCast, Finset.sum_filter]
  constructor
  · exact Finset.sum_nonneg fun n hn => by split_ifs <;> positivity
  · calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 x, L Y := by
        apply Finset.sum_le_sum
        intro n hn
        split_ifs
        · have hn' := Finset.mem_Icc.mp hn
          exact vonMangoldt_le_log.trans (Real.log_le_log
            (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn'.2.trans hx))
        · exact hlog
      _ = x * L Y := by simp

/-- Page 361, display 16, the uniform natural cutoff Siegel and Walfisz input.
This uses the progression sum of HeathBrown1985 and implies the natural cutoff input. -/
theorem siegel_walfisz_uniform : ∀ D A' : ℝ, 0 < D → 0 < A' → ∃ C : ℝ, 0 ≤ C ∧
    ∀ Y : ℕ, 2 ≤ Y → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ L Y ^ D → ∀ b : ℕ, b < q →
      Nat.Coprime b q → ∀ x : ℕ, x ≤ Y →
        |LeanLab.HeathBrown1985.psi x q b - x / (Nat.totient q : ℝ)| ≤ C * Y / L Y ^ A' := by
  intro D A hD hA
  obtain ⟨c, hc, K, hSW⟩ := LeanLab.PNTPort.PsiChi.siegelWalfisz (D + 1) (by linarith)
  obtain ⟨KE, hKE, hE⟩ := LeanLab.PNTPort.BV.exp_neg_sqrt_log_le c hc A
  obtain ⟨K0, hK0, h0⟩ := LeanLab.PNTPort.BV.log_rpow_le_sqrt A
  obtain ⟨K1, hK1, h1⟩ := LeanLab.PNTPort.BV.log_rpow_le_sqrt (A + 1)
  let T : ℝ := Real.exp (max ((2 : ℝ) ^ D) 2)
  let Cs : ℝ := T * (K0 + K1)
  let Cl : ℝ := max K 0 * KE * (2 : ℝ) ^ A
  have hT : 0 < T := Real.exp_pos _
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity
  refine ⟨Cs + Cl, add_nonneg hCs hCl, ?_⟩
  intro Y hY q hq hqY b hb hcop x hxY
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlog : 0 < L Y := L_pos hY
  have hpow : 0 < L Y ^ A := Real.rpow_pos_of_pos hlog _
  have hsqrt : 1 ≤ Real.sqrt (Y : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hT1 : 1 ≤ T := Real.one_le_exp (by linarith [le_max_right ((2 : ℝ) ^ D) 2])
  have hphi : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.totient_pos.mpr (by omega : 0 < q))
  have hfrac : (x : ℝ) / Nat.totient q ≤ x := by
    exact div_le_self (Nat.cast_nonneg _) hphi
  have hbounds := psi_bounds hY hxY q b
  have htriv : |LeanLab.HeathBrown1985.psi x q b - x / (Nat.totient q : ℝ)| ≤ (x : ℝ) * (L Y + 1) := by
    calc
      _ ≤ |LeanLab.HeathBrown1985.psi x q b| + |(x : ℝ) / Nat.totient q| := abs_sub _ _
      _ ≤ x * L Y + x := by
        rw [abs_of_nonneg hbounds.1, abs_of_nonneg (by positivity)]
        exact add_le_add hbounds.2 hfrac
      _ = _ := by ring
  by_cases hx : (x : ℝ) ≤ T * Real.sqrt (Y : ℝ)
  · have hpoly : (L Y + 1) * L Y ^ A ≤ (K0 + K1) * Real.sqrt (Y : ℝ) := by
      have h01 := add_le_add (h0 (Y : ℝ) hYr) (h1 (Y : ℝ) hYr)
      change L Y ^ A + L Y ^ (A + 1) ≤ _ at h01
      rw [Real.rpow_add_one hlog.ne'] at h01
      convert h01 using 1 <;> ring
    have hscale := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ T * Real.sqrt (Y : ℝ) by positivity)
    have hsmall : (T * Real.sqrt (Y : ℝ) * (L Y + 1)) * L Y ^ A ≤ Cs * Y := by
      calc
        _ ≤ (T * Real.sqrt (Y : ℝ)) * ((K0 + K1) * Real.sqrt (Y : ℝ)) := by
          simpa only [mul_assoc] using hscale
        _ = T * (K0 + K1) * (Real.sqrt (Y : ℝ)) ^ 2 := by ring
        _ = Cs * Y := by rw [Real.sq_sqrt hY0.le]
    have hh : |LeanLab.HeathBrown1985.psi x q b - x / (Nat.totient q : ℝ)| ≤ Cs * Y / L Y ^ A := by
      apply (le_div_iff₀ hpow).mpr
      calc
        _ ≤ ((x : ℝ) * (L Y + 1)) * L Y ^ A := mul_le_mul_of_nonneg_right htriv hpow.le
        _ ≤ (T * Real.sqrt (Y : ℝ) * (L Y + 1)) * L Y ^ A := by gcongr
        _ ≤ _ := hsmall
    exact hh.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Cs ≤ Cs + Cl) (Nat.cast_nonneg _)) hpow.le)
  · have hxlarge : T * Real.sqrt (Y : ℝ) < x := lt_of_not_ge hx
    have hTx : T < x := (le_mul_of_one_le_right hT.le hsqrt).trans_lt hxlarge
    have hx0 : (0 : ℝ) < x := hT.trans hTx
    have hT2 : (2 : ℝ) ≤ T := by
      have hexp : (2 : ℝ) ≤ Real.exp 2 := by nlinarith [Real.add_one_le_exp (2 : ℝ)]
      exact hexp.trans (Real.exp_le_exp.mpr (le_max_right _ _))
    have hx2 : (2 : ℝ) ≤ x := hT2.trans hTx.le
    have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
    have hlogT : Real.log T = max ((2 : ℝ) ^ D) 2 := Real.log_exp _
    have hcoef : (2 : ℝ) ^ D ≤ Real.log (x : ℝ) := by
      have ht := Real.log_le_log hT hTx.le
      rw [hlogT] at ht
      exact (le_max_left _ _).trans ht
    have hsx : Real.sqrt (Y : ℝ) ≤ x :=
      (le_mul_of_one_le_left (Real.sqrt_nonneg _) hT1).trans hxlarge.le
    have hlogs : L Y ≤ 2 * Real.log (x : ℝ) := by
      have ht := Real.log_le_log (Real.sqrt_pos.mpr hY0) hsx
      rw [Real.log_sqrt hY0.le] at ht
      change Real.log (Y : ℝ) ≤ _
      linarith
    have hmod : (q : ℝ) ≤ Real.log (x : ℝ) ^ (D + 1) := by
      calc
        _ ≤ L Y ^ D := hqY
        _ ≤ (2 * Real.log (x : ℝ)) ^ D := Real.rpow_le_rpow hlog.le hlogs hD.le
        _ = (2 : ℝ) ^ D * Real.log (x : ℝ) ^ D := Real.mul_rpow (by norm_num) hlx.le
        _ ≤ Real.log (x : ℝ) * Real.log (x : ℝ) ^ D := by gcongr
        _ = Real.log (x : ℝ) ^ (D + 1) := by rw [Real.rpow_add_one hlx.ne']; ring
    have hpoint := hSW (x : ℝ) hx2 q b hq hcop hmod
    have hlogpow : L Y ^ A ≤ (2 : ℝ) ^ A * Real.log (x : ℝ) ^ A := by
      calc
        _ ≤ (2 * Real.log (x : ℝ)) ^ A := Real.rpow_le_rpow hlog.le hlogs hA.le
        _ = _ := Real.mul_rpow (by norm_num) hlx.le
    have hxpow : 0 < Real.log (x : ℝ) ^ A := Real.rpow_pos_of_pos hlx _
    have hratio : KE / Real.log (x : ℝ) ^ A ≤ KE * (2 : ℝ) ^ A / L Y ^ A := by
      rw [div_le_div_iff₀ hxpow hpow]
      calc
        KE * L Y ^ A ≤ KE * ((2 : ℝ) ^ A * Real.log (x : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_left hlogpow hKE.le
        _ = _ := by ring
    have hdecay := (hE (x : ℝ) hx2).trans hratio
    have hxYr : (x : ℝ) ≤ Y := by exact_mod_cast hxY
    calc
      _ ≤ K * x * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) := hpoint
      _ ≤ max K 0 * x * (KE * (2 : ℝ) ^ A / L Y ^ A) := by
        calc
          _ ≤ max K 0 * x * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left K 0) (Nat.cast_nonneg x)) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ ≤ max K 0 * Y * (KE * (2 : ℝ) ^ A / L Y ^ A) := by gcongr
      _ = Cl * Y / L Y ^ A := by dsimp [Cl]; ring
      _ ≤ (Cs + Cl) * Y / L Y ^ A := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Cl ≤ Cs + Cl) (Nat.cast_nonneg Y)) hpow.le

#print axioms psi_bounds
#print axioms siegel_walfisz_uniform
end
end LeanLab.PerelliPintz1992.Decomp544b
