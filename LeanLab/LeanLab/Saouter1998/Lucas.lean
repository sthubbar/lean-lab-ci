/-
Saouter 1998, P0018, unit U-0360, run 20261017T2003Z-30240. Saouter checked odd Goldbach to
10^20 by a ladder of certified primes on top of an even Goldbach range. Here the same method
in the Lean kernel: a Boolean Lucas certificate per rung, CertDef.lean, proved sound once, so a
whole ladder block is checked by one `decide +kernel`. Every rung p has p - 1 factored over
primes below 1000, each factor checked by trial division.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Verifications.Pratt
import LeanLab.HelfgottPlatt.Ladder
import LeanLab.Saouter1998.CertDef

namespace LeanLab.Saouter1998

open LeanLab.Verifications.Pratt LeanLab.HelfgottPlatt

theorem pm_eq : ∀ f a e m, Core.pm f a e m = LeanLab.Verifications.Pratt.pm f a e m := by
  intro f
  induction f with
  | zero => intro a e m; rfl
  | succ k ih => intro a e m; simp only [Core.pm, LeanLab.Verifications.Pratt.pm, ih]

theorem noDiv_eq (n : ℕ) : ∀ f d, Core.noDiv n f d = LeanLab.noDivFrom n f d := by
  intro f
  induction f with
  | zero => intro d; rfl
  | succ k ih => intro d; simp only [Core.noDiv, LeanLab.noDivFrom, ih]

theorem primeB_eq (n : ℕ) : Core.primeB n = LeanLab.primeB n := by
  simp only [Core.primeB, LeanLab.primeB, noDiv_eq]

theorem prodPow_eq : ∀ L : List (ℕ × ℕ), Core.prodPow L = (L.map fun x => x.1 ^ x.2).prod
  | [] => rfl
  | x :: t => by simp [Core.prodPow, prodPow_eq t]

/-- A checked certificate certifies a prime. -/
theorem prime_of_certB {c : Core.Cert} (h : Core.certB c = true) : c.1.Prime := by
  obtain ⟨p, a, L⟩ := c
  simp only [Core.certB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨_, h64⟩, hprod⟩, hpr⟩, hpow⟩, hnot⟩ := h
  rw [pm_eq] at hpow
  simp only [pm_eq] at hnot
  exact pratt p a L h64 (by rw [← prodPow_eq]; exact hprod)
    (fun x hx => primeB_sound (by rw [← primeB_eq]; exact hpr x hx)) hpow hnot

/-- Every prime of a checked certificate list is prime. -/
theorem all_prime_of_certs {C : List Core.Cert} (h : C.all Core.certB = true) :
    ∀ p ∈ C.map Prod.fst, p.Prime := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact prime_of_certB (List.all_eq_true.mp h c hc)

end LeanLab.Saouter1998
