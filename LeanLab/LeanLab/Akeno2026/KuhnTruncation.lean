/-
P0087 Akeno 2026 page 32, vanishing of T_r above r = 10.
This is a pointwise simplex proof and does not assume the general integral reduction.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.KuhnTail
import LeanLab.Akeno2026.KuhnPointwise
import LeanLab.Akeno2026.AppendixStatements

namespace LeanLab.Akeno2026.Thm12Numerics
open Finset

theorem kuhnG_eq_zero_of_many (n : ℕ) (hn : 9 ≤ n) (u : Fin (n + 2) → ℝ)
    (hm : Monotone u) (hu : ∀ i, 0 ≤ u i)
    (hfirst : 1 / 33.5 ≤ u ⟨0, by omega⟩) (hsum : ∑ i, u i = 1) :
    kuhnG 9.5 u = 0 := by
  have hsecond : u ⟨1, by omega⟩ ≤ 1 / 9.5 := by
    by_contra h
    have ht : ∀ i : Fin (n + 1), (1 / 9.5 : ℝ) ≤ u i.succ := by
      intro i
      have hi : (⟨1, by omega⟩ : Fin (n + 2)) ≤ i.succ := by
        change 1 ≤ i.val + 1
        omega
      exact (le_of_lt (lt_of_not_ge h)).trans (hm hi)
    have htail : ((n + 1 : ℕ) : ℝ) * (1 / 9.5) ≤ ∑ i : Fin (n + 1), u i.succ := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => ht i)
    have hc : (10 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 10 ≤ n + 1 by omega)
    rw [Fin.sum_univ_succ] at hsum
    change u ⟨0, by omega⟩ + (∑ i : Fin (n + 1), u i.succ) = 1 at hsum
    nlinarith
  have hfirst' : u ⟨0, by omega⟩ ≤ 1 / 9.5 :=
    (hm (show (⟨0, by omega⟩ : Fin (n + 2)) ≤ ⟨1, by omega⟩ from by change (0 : ℕ) ≤ 1; omega)).trans hsecond
  rw [kuhnG_ordered n 9.5 u hm hu,
    ite_eq_right (not_lt.mpr hfirst'), ite_eq_right (not_lt.mpr hsecond)]

end LeanLab.Akeno2026.Thm12Numerics

namespace LeanLab.Akeno2026.Appendix
open MeasureTheory LeanLab.Akeno2026.Thm12Numerics

theorem simplexIntegral_kuhn_eq_zero (n : ℕ) (hn : 9 ≤ n) :
    simplexIntegral (n + 1) 33.5 (kuhnG 9.5) = 0 := by
  unfold simplexIntegral
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro v hv
  have hu : ∀ i, 0 ≤ simplexCoords v i := by
    intro i
    have hi := (hv.1 i).1
    linarith
  rw [kuhnG_eq_zero_of_many n hn (simplexCoords v) hv.2 hu
    (hv.1 ⟨0, by omega⟩).1 (simplexCoords_sum v), zero_div]

end LeanLab.Akeno2026.Appendix

namespace LeanLab.Akeno2026.KuhnTail
open LeanLab.Akeno2026.SieveFns Set intervalIntegral

theorem kuhnTr_eq_zero_of_ge_eleven (r : ℕ) (hr : 11 ≤ r) : kuhnTr r = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 3 := ⟨r - 3, by omega⟩
  have hn : (8 : ℝ) ≤ n := by exact_mod_cast (show 8 ≤ n by omega)
  have hbase : cR (n + 3) (19 / 2) = 0 := by
    convert cR_eq_zero_of_le (n + 1) (x := 19 / 2) (by push_cast; linarith) using 1
  have hint : (∫ u in (17 / 2 : ℝ)..(1235 / 134 : ℝ),
      cR (n + 3 - 1) u / (u * (19 / 2 - u))) = 0 := by
    calc
      (∫ u in (17 / 2 : ℝ)..(1235 / 134 : ℝ), cR (n + 3 - 1) u / (u * (19 / 2 - u))) = ∫ _u in (17 / 2 : ℝ)..(1235 / 134 : ℝ), (0 : ℝ) := by
        apply integral_congr
        intro u hu
        rw [uIcc_of_le (by norm_num : (17 / 2 : ℝ) ≤ 1235 / 134)] at hu
        have hz : cR (n + 2) u = 0 := cR_eq_zero_of_le n (by linarith [hu.2])
        simpa using congrArg (fun v : ℝ => v / (u * (19 / 2 - u))) hz
      _ = 0 := by simp
  simp only [kuhnTr, hbase, hint, mul_zero, add_zero]

end LeanLab.Akeno2026.KuhnTail
