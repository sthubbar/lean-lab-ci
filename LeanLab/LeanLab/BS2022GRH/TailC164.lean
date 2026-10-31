/- AI wrote the Lean code for CODEX task164.
Elementary closure of the reciprocal prime tail in DecompJ278.
Journal display 6 p. 1221. Goldbach is open. -/
import LeanLab.BS2022GRH.FiniteC164
namespace LeanLab.BS2022GRH.TailC164
open Real Finset Classical Cert1575 Cert1575Defs
/-- A number between 400 and 160000 coprime to 400 factorial is prime.
A composite would have a prime factor at most 400. -/
theorem prime_of_wheel (n : ℕ) (hn : 400 < n) (hn1 : n < 160000)
    (hc : Nat.Coprime (fac 400) n) : n.Prime := by
  have hmin : 400 < n.minFac := by
    rw [fac_eq] at hc
    exact (Nat.coprime_factorial_iff (by omega : n ≠ 1)).mp hc.symm
  by_contra hp
  have hs := Nat.minFac_sq_le_self (by omega : 0 < n) hp
  nlinarith
/-- Each integer upper term is at most the true prime term times the scale plus one. -/
theorem term_le (M n : ℕ) (hn : 400 < n) (hn1 : n < 160000) :
    (term (fac 400) M n : ℝ) ≤ (M : ℝ) * a n + 1 := by
  by_cases hg : Nat.gcd (fac 400) n = 1
  · have hp := prime_of_wheel n hn hn1 hg
    have ht : term (fac 400) M n = M / (n * n) + 1 := by simp [term, hg]
    rw [ht]
    push_cast
    have hh : ((M / (n * n) : ℕ) : ℝ) ≤ (M : ℝ) / (n : ℝ) ^ 2 := by
      simpa only [Nat.cast_mul, pow_two] using
        (Nat.cast_div_le (m := M) (n := n * n) : ((M / (n * n) : ℕ) : ℝ) ≤ (M : ℝ) / (n * n : ℕ))
    simp only [a, if_pos hp]
    linarith [show (M : ℝ) / (n : ℝ) ^ 2 = (M : ℝ) * (1 / (n : ℝ) ^ 2) by ring]
  · have ht : term (fac 400) M n = 0 := by simp [term, hg]
    rw [ht]
    norm_num only [Nat.cast_zero]
    nlinarith [mul_nonneg (Nat.cast_nonneg M) (a_nonneg n)]
/-- Reverse window estimate, with at most two units of rounding per block. -/
theorem window_lower (M : ℕ) : ∀ f lo, lo % 6 = 1 → 400 < lo → lo + 6 * f ≤ 160000 →
    (T (fac 400) M f lo : ℝ) ≤ (M : ℝ) * ∑ n ∈ Ico lo (lo + 6 * f), a n + 2 * f := by
  intro f
  induction f with
  | zero => intro lo _ _ _; simp [T]
  | succ f ih =>
    intro lo h6 hlo hhi
    rw [← Finset.sum_Ico_consecutive a (show lo ≤ lo + 6 by omega)
      (show lo + 6 ≤ lo + 6 * (f + 1) by omega), block6 lo h6 (by omega)]
    have h1 := term_le M lo hlo (by omega)
    have h2 := term_le M (lo + 4) (by omega) (by omega)
    have h3 := ih (lo + 6) (by omega) (by omega) (by omega)
    rw [show lo + 6 + 6 * f = lo + 6 * (f + 1) by ring] at h3
    simp only [T]
    push_cast
    nlinarith
/-- A certified lower bound for the prime reciprocal block below 100000. -/
theorem prefix_lower :
    (7884029693000000 - 32832 : ℝ) / 10 ^ 20 ≤ ∑ n ∈ Ico 1501 99997, a n := by
  have hc := CertC164.lower_window
  rw [inner_eq] at hc
  simp only [zero_add] at hc
  generalize hV : T (fac 400) (10 ^ 20) 16416 1501 = V at hc
  have hcr : (7884029693000000 : ℝ) ≤ V := by exact_mod_cast hc
  have hw := window_lower (10 ^ 20) 16416 1501 (by norm_num) (by norm_num) (by norm_num)
  rw [hV] at hw
  norm_num at hw
  have : (0 : ℝ) < 10 ^ 20 := by norm_num
  rw [div_le_iff₀ this]
  norm_num
  linarith only [hcr, hw]
/-- The exact strict prime tail bound stated in the existing decomposition. -/
theorem tail_sum_le :
    ∑' p : {p : ℕ // p.Prime ∧ 100000 ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2 < 8.1e-7 := by
  have hb : ∑' p : {p : ℕ // p.Prime ∧ 100000 ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2 ≤
      (8.09e-7 : ℝ) := by
    apply Real.tsum_le_of_sum_le (fun _ => by positivity)
    intro u
    set X := 9003001 + u.sup (fun x => x.1) with hX
    have himg : ∑ x ∈ u, 1 / ((x : ℕ) : ℝ) ^ 2 = ∑ n ∈ u.image (fun x => x.1), a n := by
      rw [Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
      apply Finset.sum_congr rfl
      intro x _
      simp [a, x.2.1]
    rw [himg]
    have hd : Disjoint (Ico 1501 99997) (u.image (fun x => x.1)) := by
      apply Finset.disjoint_left.mpr
      intro n hn hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      have hh : 100000 ≤ x.1 := by exact_mod_cast x.2.2
      have := (Finset.mem_Ico.mp hn).2
      omega
    have hsub : (Ico 1501 99997) ∪ u.image (fun x => x.1) ⊆
        Ico 1501 (9003001 + (X - 9003001) + 1) := by
      intro n hn
      rcases Finset.mem_union.mp hn with hp | hu
      · have := Finset.mem_Ico.mp hp
        simp only [Finset.mem_Ico]
        omega
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        have hh : 100000 ≤ x.1 := by exact_mod_cast x.2.2
        have hle : x.1 ≤ u.sup (fun x => x.1) := Finset.le_sup hx
        simp only [Finset.mem_Ico]
        rw [hX]
        omega
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := a) hsub (fun n _ _ => a_nonneg n)
    rw [Finset.sum_union hd] at hs
    have hlarge : ∑ n ∈ Ico 1501 (9003001 + (X - 9003001) + 1), a n ≤
        7963599791126110 / 10 ^ 20 +
          ((89 / 80 * 9003001 - 8191444) / (16 * 9003001 ^ 2) + 89 / 80 / (16 * 9003001)) := by
      rw [← Finset.sum_Ico_consecutive a (by norm_num : 1501 ≤ 9003001) (by omega)]
      exact add_le_add head_le (tail_le _)
    have hp := prefix_lower
    norm_num at hp hlarge
    linarith only [hp, hlarge, hs]
  exact hb.trans_lt (by norm_num)
end LeanLab.BS2022GRH.TailC164
#print axioms LeanLab.BS2022GRH.TailC164.prime_of_wheel
#print axioms LeanLab.BS2022GRH.TailC164.term_le
#print axioms LeanLab.BS2022GRH.TailC164.window_lower
#print axioms LeanLab.BS2022GRH.TailC164.prefix_lower
#print axioms LeanLab.BS2022GRH.TailC164.tail_sum_le
