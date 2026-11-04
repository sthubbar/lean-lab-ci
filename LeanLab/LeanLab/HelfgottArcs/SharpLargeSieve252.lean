/-
Sharp additive large sieve input for the Decomp119 Type II unit.
Source: P0013 page 45, proof of Lemma 4.3, quoting Montgomery and Vaughan 1974,
Hilbert's inequality, Journal of the London Mathematical Society, volume 8, pages 73 to 82.
The lab's proved large sieve has N plus two over delta instead.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.PNTPort.LargeSieve.Parseval
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs.Decomp119
open Finset

/-- LEAF. P0013 page 45, optimal additive large sieve used in Lemma 4.3.
Montgomery and Vaughan 1974, Hilbert's inequality, pages 73 to 82.
The positive length and delta at most one restrictions cover singleton frequency sets. -/
theorem sharp_additive_large_sieve252 (s : Finset ℕ) (θ : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' →
      δ ≤ |θ r - θ r' - round (θ r - θ r')|)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M+N), a n * e ((n:ℝ)*θ r)‖^2 ≤
      ((N:ℝ)-1+1/δ) * ∑ n ∈ Ioc M (M+N), ‖a n‖^2 := by
  sorry

/-- Single frequency energy bound, derived from P0013 page 45 by Cauchy Schwarz. -/
theorem single_frequency_energy252 (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Ioc M (M+N), a n * e ((n:ℝ)*θ)‖^2 ≤
      (N:ℝ) * ∑ n ∈ Ioc M (M+N), ‖a n‖^2 := by
  have ht : ‖∑ n ∈ Ioc M (M+N), a n * e ((n:ℝ)*θ)‖ ≤ ∑ n ∈ Ioc M (M+N), ‖a n‖ := by
    simpa only [norm_mul, show ∀ t, ‖e t‖ = 1 from fun t => by simp [e, Complex.norm_exp], mul_one]
      using norm_sum_le (Ioc M (M+N)) (fun n => a n * e ((n:ℝ)*θ))
  have hc := sum_mul_sq_le_sq_mul_sq (Ioc M (M+N)) (fun _ => (1:ℝ)) (fun n => ‖a n‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, Int.card_Ioc, add_sub_cancel_left,
    Int.toNat_natCast] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hc

/-- Distinct residues preserve coefficient energy, a rational base case for P0013 page 45. -/
theorem residue_energy252 (I : Finset ℤ) (a : ℤ → ℂ) (q : ℕ) (hq : 0 < q)
    (hI : Set.InjOn (fun n : ℤ => n % (q:ℤ)) I) :
    ∑ b ∈ range q, ‖∑ n ∈ I.filter (fun n => n % (q:ℤ) = b), a n‖^2 =
      ∑ n ∈ I, ‖a n‖^2 := by
  have hsmall (b : ℕ) :
      ‖∑ n ∈ I.filter (fun n => n % (q:ℤ) = b), a n‖^2 =
        ∑ n ∈ I.filter (fun n => n % (q:ℤ) = b), ‖a n‖^2 := by
    by_cases hb : ∃ n ∈ I, n % (q:ℤ) = b
    · obtain ⟨n, hn, hnres⟩ := hb
      have hf : I.filter (fun n => n % (q:ℤ) = b) = {n} := by
        ext m
        simp only [mem_filter, mem_singleton]
        constructor
        · intro hm
          exact hI hm.1 hn (hm.2.trans hnres.symm)
        · intro he; subst m; exact ⟨hn, hnres⟩
      simp [hf]
    · have hf : I.filter (fun n => n % (q:ℤ) = b) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn
        exact hb ⟨n, (mem_filter.mp hn).1, (mem_filter.mp hn).2⟩
      simp [hf]
  simp_rw [hsmall, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  have hn0 : 0 ≤ n % (q:ℤ) := Int.emod_nonneg n (by exact_mod_cast hq.ne')
  have hnq : n % (q:ℤ) < q := Int.emod_lt_of_pos n (by exact_mod_cast hq)
  have hb : (n % (q:ℤ)).toNat ∈ range q := by rw [mem_range]; omega
  rw [sum_eq_single (n % (q:ℤ)).toNat]
  · rw [if_pos (by omega)]
  · intro b hb hne
    rw [if_neg (by intro hh; apply hne; omega)]
  · intro hnot; exact (hnot hb).elim

/-- Exact rational grid energy with distinct input residues, derived for P0013 page 45.
This does not prove the perturbation step of the sharp large sieve. -/
theorem rational_grid_energy252 (I : Finset ℤ) (a : ℤ → ℂ) (q : ℕ) (hq : 0 < q)
    (hI : Set.InjOn (fun n : ℤ => n % (q:ℤ)) I) :
    ∑ c ∈ range q, ‖∑ n ∈ I, a n * e ((n:ℝ)*c/q)‖^2 =
      (q:ℝ) * ∑ n ∈ I, ‖a n‖^2 := by
  have he (t : ℝ) : LeanLab.PNTPort.LargeSieve.e t = e t := by
    unfold LeanLab.PNTPort.LargeSieve.e e
    congr 1
    push_cast
    ring
  have hp := LeanLab.PNTPort.LargeSieve.parseval_mod I a hq
  simp only [he, LeanLab.PNTPort.LargeSieve.resSum] at hp
  rw [residue_energy252 I a q hq hI] at hp
  exact hp


end LeanLab.HelfgottArcs.Decomp119
