import LeanLab.Ternary78.Paper104

/-
AI wrote this Lean code. Binary Goldbach is open.
Decomposition of P0099 Theorem 3, printed page 13.
The analytic and computed prime ladder leaves remain cited obligations.
-/

namespace LeanLab.Ternary78.Paper104

/-- LEAF. P0099 page 12 Theorem 2 with the page 11 Table 1 first row.
The analytic range starts at 10^20, exactly as printed in Theorem 2.
This cited input uses the zero verification of Wedeniwski, reference 24,
and the Schoenfeld estimates, reference 18. It is not proved here. -/
theorem analytic_table46 :
    ∀ x : ℝ, (10 : ℝ) ^ 20 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 81353847) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  sorry

/-- LEAF. P0099 pages 25 and 26, finite prime ladder for Theorem 3.
Reverse the descending sequence in the paper. The finite certificate is absent.
Its primality tests use Brillhart, Lehmer and Selfridge, reference 6,
and Jaeschke, reference 11. No recomputation is claimed. -/
theorem computed_prime_ladder :
    ∃ n : ℕ, ∃ p : ℕ → ℕ,
      (∀ i, i ≤ n → (p i).Prime) ∧
      (p 0 : ℝ) ≤ 10726905041 ∧ (10 : ℝ) ^ 20 ≤ p n ∧
      ∀ i, i < n → (p (i + 1) : ℝ) * (1 - 1 / 28314000) ≤ p i := by
  sorry

/-- LEAF. P0099 page 12, log of 10^20 exceeds the first Table 1 endpoint 46. -/
theorem table46_below_join : Real.exp 46 < (10 : ℝ) ^ 20 := by
  have he : Real.exp 46 = Real.exp 1 ^ 46 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  calc
    Real.exp 1 ^ 46 ≤ (2.719 : ℝ) ^ 46 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 46
    _ < (10 : ℝ) ^ 20 := by norm_num

#print axioms table46_below_join

/-- LEAF. P0099 page 13 footnote 1, the first table interval is narrower
than the main theorem interval at every nonnegative x. -/
theorem table46_interval_inclusion {x : ℝ} (hx : 0 ≤ x) :
    x * (1 - 1 / 28314000) ≤ x * (1 - 1 / 81353847) := by
  exact mul_le_mul_of_nonneg_left (by norm_num) hx

#print axioms table46_interval_inclusion

/-- LEAF. P0099 pages 25 and 26, the elementary real interval coverage
implicit in the finite prime ladder algorithm. No monotonicity is needed. -/
theorem ladder_covers {n : ℕ} {p : ℕ → ℕ}
    (hprime : ∀ i, i ≤ n → (p i).Prime)
    (hstep : ∀ i, i < n → (p (i + 1) : ℝ) * (1 - 1 / 28314000) ≤ p i)
    {x : ℝ} (hfirst : (p 0 : ℝ) ≤ x) (hlast : x ≤ p n) :
    ∃ q : ℕ, q.Prime ∧ x * (1 - 1 / 28314000) < (q : ℝ) ∧ (q : ℝ) ≤ x := by
  induction n with
  | zero =>
    have hx : x = p 0 := le_antisymm hlast hfirst
    refine ⟨p 0, hprime 0 le_rfl, ?_, hfirst⟩
    have hpos : (0 : ℝ) < p 0 := by exact_mod_cast (hprime 0 le_rfl).pos
    rw [hx]
    nlinarith
  | succ n ih =>
    by_cases hx : x ≤ p n
    · exact ih (fun i hi => hprime i (by omega))
        (fun i hi => hstep i (by omega)) hx
    · have hx' : (p n : ℝ) < x := lt_of_not_ge hx
      by_cases heq : x = p (n + 1)
      · refine ⟨p (n + 1), hprime (n + 1) le_rfl, ?_, heq.ge⟩
        have hpos : (0 : ℝ) < p (n + 1) := by
          exact_mod_cast (hprime (n + 1) le_rfl).pos
        rw [heq]
        nlinarith
      · refine ⟨p n, hprime n (by omega), ?_, hx'.le⟩
        have hstrict : x < p (n + 1) := lt_of_le_of_ne hlast heq
        have hmul := mul_lt_mul_of_pos_right hstrict
          (by norm_num : (0 : ℝ) < 1 - 1 / 28314000)
        exact hmul.trans_le (hstep n (by omega))

#print axioms ladder_covers

/-- Assembly of P0099 Theorem 3 with exactly the cited Prop as conclusion.
CONDITIONAL ON analytic_table46 and computed_prime_ladder.
The assembly itself contains no sorry. -/
theorem primeInterval_decomposed : PrimeInterval := by
  intro x hx
  by_cases hlarge : (10 : ℝ) ^ 20 ≤ x
  · obtain ⟨p, hp, hlo, hhi⟩ := analytic_table46 x hlarge
    exact ⟨p, hp, (table46_interval_inclusion (by linarith)).trans_lt hlo, hhi⟩
  · obtain ⟨n, p, hp, hfirst, hlast, hstep⟩ := computed_prime_ladder
    exact ladder_covers hp hstep (hfirst.trans hx.le) ((le_of_not_ge hlarge).trans hlast)

#print axioms primeInterval_decomposed

/-- P0099 page 13 Theorem 3 from the conservative page 12 Theorem 2 domain
and the finite prime ladder certificate. CONDITIONAL ON the two explicit inputs.
This theorem has clean axioms and does not use the stronger analytic_table46 leaf. -/
theorem primeInterval_from_conservative_inputs
    (hA : ∀ x : ℝ, (10 : ℝ) ^ 20 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 81353847) < (p : ℝ) ∧ (p : ℝ) ≤ x)
    (hC : ∃ n : ℕ, ∃ p : ℕ → ℕ,
      (∀ i, i ≤ n → (p i).Prime) ∧
      (p 0 : ℝ) ≤ 10726905041 ∧ (10 : ℝ) ^ 20 ≤ p n ∧
      ∀ i, i < n → (p (i + 1) : ℝ) * (1 - 1 / 28314000) ≤ p i) : PrimeInterval := by
  intro x hx
  by_cases hlarge : (10 : ℝ) ^ 20 ≤ x
  · obtain ⟨p, hp, hlo, hhi⟩ := hA x hlarge
    exact ⟨p, hp, (table46_interval_inclusion (by linarith)).trans_lt hlo, hhi⟩
  · obtain ⟨n, p, hp, hfirst, hlast, hstep⟩ := hC
    exact ladder_covers hp hstep (hfirst.trans hx.le) ((le_of_not_ge hlarge).trans hlast)

#print axioms primeInterval_from_conservative_inputs

end LeanLab.Ternary78.Paper104
