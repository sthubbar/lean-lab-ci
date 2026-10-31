/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 pages 2 and 3, the finite C3 sum.
This connects the actual weight and multiplicative orders to the D = 11 proof.
-/
import LeanLab.PlattTrudgian2014.PaperInputs

namespace LeanLab.PlattTrudgian2014

open Finset

set_option maxRecDepth 10000 in
theorem paperC3Finite_eleven_eq (K N : ℕ) :
    paperC3Finite 11 K N =
      Section2.C3sum11Full K (N : ZMod 3) (N : ZMod 5) (N : ZMod 7) (N : ZMod 11) := by
  have h3 : paperWeight 3 = 1 := by
    rw [paperWeight_odd_prime (by decide : Nat.Prime 3) (by decide)]; norm_num
  have h5 : paperWeight 5 = 1 / 3 := by
    rw [paperWeight_odd_prime (by decide : Nat.Prime 5) (by decide)]; norm_num
  have h7 : paperWeight 7 = 1 / 5 := by
    rw [paperWeight_odd_prime (by decide : Nat.Prime 7) (by decide)]; norm_num
  have h11 : paperWeight 11 = 1 / 9 := by
    rw [paperWeight_odd_prime (by decide : Nat.Prime 11) (by decide)]; norm_num
  have h2 : paperWeight 2 = 0 := paperWeight_even (by decide)
  have h4 : paperWeight 4 = 0 := paperWeight_even (by decide)
  have h6 : paperWeight 6 = 0 := paperWeight_even (by decide)
  have h8 : paperWeight 8 = 0 := paperWeight_even (by decide)
  have h10 : paperWeight 10 = 0 := paperWeight_even (by decide)
  have h9 : paperWeight 9 = 0 := paperWeight_not_squarefree (by decide +kernel)
  have he1 : orderOf (2 : ZMod 1) = 1 := by
    rw [show (2 : ZMod 1) = 1 from Subsingleton.elim _ _, orderOf_one]
  have hH1 : Section2.H 1 1 K (N : ZMod 1) = 1 := by
    have hp : ∀ v : Fin K → Fin 1,
        (N : ZMod 1) = ∑ i, (2 : ZMod 1) ^ ((v i : ℕ) + 1) := fun _ => Subsingleton.elim _ _
    have hf : (univ.filter fun v : Fin K → Fin 1 =>
        (N : ZMod 1) = ∑ i, (2 : ZMod 1) ^ ((v i : ℕ) + 1)) = univ :=
      filter_eq_self.mpr (fun v _ => hp v)
    exact (congrArg Finset.card hf).trans (by simp)
  unfold paperC3Finite
  have hset : Icc 1 11 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset ℕ) := by decide
  norm_num [hset,
    paperWeight_one, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, he1, hH1,
    Section2.eps_3, Section2.eps_5, Section2.eps_7, Section2.eps_11]
  unfold Section2.C3sum11Full Section2.C3sum11
  ring

theorem paperC3Finite_eleven_lower (K N : ℕ) (hK : 6 ≤ K) :
    2.8650 ≤ paperC3Finite 11 K N := by
  rw [paperC3Finite_eleven_eq]
  exact Section2.C3_D11_full_lower K hK _ _ _ _

theorem paperC3Finite_lower {D K : ℕ} (hD : 11 ≤ D) (hK : 6 ≤ K) (N : ℕ) :
    2.8650 ≤ paperC3Finite D K N :=
  (paperC3Finite_eleven_lower K N hK).trans (paperC3Finite_mono hD K N)

#print axioms paperC3Finite_eleven_eq
#print axioms paperC3Finite_eleven_lower
#print axioms paperC3Finite_lower

end LeanLab.PlattTrudgian2014
