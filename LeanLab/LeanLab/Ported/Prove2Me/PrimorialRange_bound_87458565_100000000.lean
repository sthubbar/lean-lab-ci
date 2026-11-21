/-
Ported from Prove2Me, mission 0814790f.
Source PrimorialRange_bound_87458565_100000000. Author kmehltretter82. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Zify
import LeanLab.Ported.Prove2Me.Def_ThetaCertCore
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c1
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c2
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c3
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c4
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c5
import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c3
import LeanLab.Ported.Prove2Me.PrimorialRange_bound_87458565_100000000_certificate
namespace LeanLab.Ported.Prove2Me.Task666
open Finset Real
open LeanLab.Ported.Prove2Me.Task664
open LeanLab.Ported.Prove2Me.Task664.PrimC3Cert
open DusartCert ThetaSieve
namespace PrimC6R7
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma HiInv_of_axler {x0 U0 L0 : ℕ} (hL0 : L0 - 1 ≤ x0)
    (h : (1000000 : ℝ) * Chebyshev.theta (x0 : ℝ) ≤ (U0 : ℝ)) :
    ((Q : ℝ) * th (L0 - 1) ≤ (cdiv (Q * U0) 1000000 : ℝ)) := by
  unfold th
  have hmono : Chebyshev.theta ((L0 - 1 : ℕ) : ℝ) ≤ Chebyshev.theta (x0 : ℝ) :=
    Chebyshev.theta_mono (by exact_mod_cast hL0)
  have h1 : (Q : ℝ) * Chebyshev.theta ((L0 - 1 : ℕ) : ℝ) ≤ (Q : ℝ) * ((U0 : ℝ) / 1000000) := by
    have : Chebyshev.theta (x0 : ℝ) ≤ (U0 : ℝ) / 1000000 := by linarith
    exact mul_le_mul_of_nonneg_left (hmono.trans this) (le_of_lt Q_pos)
  have h2 : (Q : ℝ) * ((U0 : ℝ) / 1000000) = ((Q * U0 : ℕ) : ℝ) / ((1000000 : ℕ) : ℝ) := by
    push_cast; ring
  have h3 := le_cdiv (Q * U0) 1000000 (by norm_num)
  linarith

private theorem ax_c1 : (154635160747 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ≤ (154642599361 : ℝ) := TaoFivePrimes.axler_chain_c1.1
private theorem ax_c2 : (1697867131810 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ≤ (1697951293771 : ℝ) := (TaoFivePrimes.axler_chain_c2 ax_c1).1
private theorem ax_c3 : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ) := (TaoFivePrimes.axler_chain_c3 ax_c2).1
private theorem ax_c4 : (52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ) := (TaoFivePrimes.axler_chain_c4 ax_c3).1
private theorem ax_top : (87444803702622 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (87458565 : ℝ) ≤ (87448235987654 : ℝ) := (TaoFivePrimes.axler_chain_c5 ax_c4).1

lemma hi_eq : cdiv (Q * 87448235987654) 1000000 = 1613135228961610762836131252 := by decide

lemma hiInv_start : ((Q : ℝ) * th (87458565 - 1) ≤ (1613135228961610762836131252 : ℝ)) := by
  simpa only [hi_eq, Nat.cast_ofNat] using (HiInv_of_axler (x0 := 87458565) (U0 := 87448235987654) (L0 := 87458565) (by omega) (by exact_mod_cast ax_top.2))

lemma cval : LLo 68 - LHi 25 = 18458400208034708012 := by decide +kernel
lemma cpos : LHi 25 ≤ LLo 68 := by decide +kernel



end PrimC6R7

theorem PrimorialRange.bound_87458565_100000000 (n : ℕ) (hn : 87458565 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  have hQ := LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.primChain_sound 48 87458565 1613135228961610762836131252
    PrimC6R7.cert_range PrimC6R7.hiInv_start n hn (by omega) (by omega)
  have hcq := LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.c_le PrimC6R7.cpos
  rw [PrimC6R7.cval] at hcq
  have h2 : (ThetaSieve.Q : ℝ) * LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.th n < ThetaSieve.Q * (n * Real.log (68 / 25)) := by
    calc (ThetaSieve.Q : ℝ) * LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.th n < (n : ℝ) * (18458400208034708012 : ℕ) := hQ
      _ ≤ (n : ℝ) * (ThetaSieve.Q * Real.log (68 / 25)) := mul_le_mul_of_nonneg_left hcq (Nat.cast_nonneg n)
      _ = ThetaSieve.Q * (n * Real.log (68 / 25)) := by ring
  exact LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.primorial_of_theta n (by omega) (lt_of_mul_lt_mul_left h2 (le_of_lt LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.Q_pos))

#print axioms PrimC6R7.ax_c1
#print axioms PrimC6R7.ax_c2
#print axioms PrimC6R7.ax_c3
#print axioms PrimC6R7.ax_c4
#print axioms PrimC6R7.ax_top

end LeanLab.Ported.Prove2Me.Task666
