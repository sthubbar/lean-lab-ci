import LeanLab.LiuWang2002.Chain666Defs
import LeanLab.Ported.Prove2Me.Def_axler_theta_chain_base
import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c3
import Mathlib.Tactic

/-!
A sharper comparison on the existing Prove2Me Axler block states.
Source Schoenfeld 1976 page 356 display 5.1 star, derived finite certificate.
No prime data are added. The existing block soundness theorem is reused.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task666
open LeanLab.Ported.Prove2Me.Task666
open AxlerChain AxlerTheta RosserSieveData RosserFastCompute RosserScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem guardGo_sound {G : Grp} {A gbase m : ℕ}
    (hm : m = mask gbase G.2.1) (hb1 : 1 ≤ gbase)
    (hsq : G.2.1 ≤ gbase * gbase) (h8 : G.2.1 ≤ 10 ^ 8) :
    ∀ (bs : List Blk) (prev L U : ℕ),
      grpGo G gbase m prev L U bs = true →
      guardGo A gbase m U bs = true →
      (∀ B ∈ bs, gbase ≤ B.1 ∧ B.1 < B.2.1 ∧ B.2.1 ≤ G.2.1) →
      (L : ℝ) ≤ S * Chebyshev.theta (prev : ℝ) →
      S * Chebyshev.theta (prev : ℝ) ≤ (U : ℝ) →
      ∀ n : ℕ, A < n → prev < n → n ≤ G.2.1 →
        Chebyshev.theta (n : ℝ) < (100063 / 100000 : ℝ) * n := by
  intro bs
  induction bs with
  | nil =>
    intro prev L U hgo _ _ _ _ n _ hn htop
    simp only [grpGo, Bool.and_eq_true, decide_eq_true_eq] at hgo
    obtain ⟨⟨heq, _⟩, _⟩ := hgo
    omega
  | cons B rest ih =>
    intro prev L U hgo hguard hbd hL hU n hA hn htop
    simp only [grpGo] at hgo
    cases he : blkOK gbase m B L U with
    | mk ok st =>
      rw [he] at hgo
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgo
      obtain ⟨⟨hprev, hok⟩, hrest⟩ := hgo
      subst prev
      have hb := hbd B (by simp)
      have hs := blkOK_spec' he hok
      have hs' := hs
      obtain ⟨w, cnt, llo, lhi, hw, hc, hl, hh, hle, hue, _⟩ := hs'
      have hue' : st.2 = U + bitCount (depthFor (B.2.1 - B.1))
          (m / 2 ^ (B.1 - gbase) % 2 ^ (B.2.1 - B.1)) * logUpNum B.2.1 := by
        simpa only [hc, hw, hh] using hue
      have hstates := blk_state hm hs hb.1 hb1 hsq hb.2.2 h8
        (by omega) hb.2.1 hL hU
      simp only [guardGo, RosserPackedBarrier.forceNat_eq] at hguard
      rw [← hue'] at hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨hcheck, hguardrest⟩ := hguard
      by_cases hin : n ≤ B.2.1
      · have hba : ¬ B.2.1 ≤ A := by omega
        rw [if_neg hba] at hcheck
        have hnat := of_decide_eq_true hcheck
        have hreal : (st.2 : ℝ) * 100000 <
            100063 * 1000000 * (max B.1 A : ℕ) := by
          norm_num [scale] at hnat
          exact_mod_cast hnat
        have hmono : S * Chebyshev.theta (n : ℝ) ≤ (st.2 : ℝ) :=
          (mul_le_mul_of_nonneg_left
            (Chebyshev.theta_mono (by exact_mod_cast hin)) S_pos.le).trans hstates.2
        have hmax : ((max B.1 A : ℕ) : ℝ) ≤ n := by
          exact_mod_cast (max_le (Nat.le_of_lt hn) (Nat.le_of_lt hA))
        have hmul := mul_le_mul_of_nonneg_left hmax
          (by norm_num : (0 : ℝ) ≤ 100063 * 1000000)
        norm_num [S, scale] at hmono
        nlinarith only [hreal, hmono, hmul]
      · exact ih B.2.1 st.1 st.2 hrest hguardrest
          (fun C hC => hbd C (by simp [hC])) hstates.1 hstates.2 n hA (by omega) htop

theorem guardGroup_bound (A : ℕ) (G : Grp)
    (hOK : grpOK G = true) (hwf : grpWF G = true) (hguard : guardGroup A G = true)
    (hL : (G.2.2.1 : ℝ) ≤ S * Chebyshev.theta (G.1 : ℝ))
    (hU : S * Chebyshev.theta (G.1 : ℝ) ≤ (G.2.2.2.1 : ℝ))
    (n : ℕ) (hA : A < n) (hn : G.1 < n) (htop : n ≤ G.2.1) :
    primorial n * 25 ^ n < 68 ^ n := by
  have hp := grpWF_spec hwf
  have hgo : grpGo G G.1 (mask G.1 G.2.1) G.1 G.2.2.1 G.2.2.2.1
      G.2.2.2.2.2.2 = true := by
    simpa only [grpOK, RosserPackedBarrier.forceNat_eq] using hOK
  have hg : guardGo A G.1 (mask G.1 G.2.1) G.2.2.2.1 G.2.2.2.2.2.2 = true := by
    simpa only [guardGroup, RosserPackedBarrier.forceNat_eq] using hguard
  have ht := guardGo_sound rfl hp.1.1 hp.1.2.2.2.1 hp.1.2.2.2.2
    _ _ _ _ hgo hg hp.2 hL hU n hA hn htop
  have hc : (100063 / 100000 : ℝ) < Real.log (68 / 25) := by
    have h := LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.c_le
      LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.cpos
    rw [LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.cval] at h
    norm_num [LeanLab.Ported.Prove2Me.Task664.ThetaSieve.Q] at h
    nlinarith
  have hn0 : 0 < n := by omega
  have hr := mul_lt_mul_of_pos_right hc (show (0 : ℝ) < n by exact_mod_cast hn0)
  apply LeanLab.Ported.Prove2Me.Task664.PrimC3Cert.primorial_of_theta n hn0
  exact lt_trans ht (by nlinarith only [hr])

end LeanLab.LiuWang2002.Task666
#print axioms LeanLab.LiuWang2002.Task666.guardGo_sound
#print axioms LeanLab.LiuWang2002.Task666.guardGroup_bound
