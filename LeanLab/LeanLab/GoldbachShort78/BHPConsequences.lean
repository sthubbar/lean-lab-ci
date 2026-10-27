import LeanLab.GoldbachShort78.BHPTiling
import LeanLab.GoldbachShort78.Growth
import LeanLab.GoldbachShort78.LiNormalization

/-!
AI wrote the Lean code, Codex task57. Binary Goldbach is OPEN.
The analytic input is the final displayed prime count in BHP 2001 p. 562.
https://doi.org/10.1112/plms/83.3.532
-/

namespace LeanLab.GoldbachShort78

/-- CONDITIONAL ON the printed BHP count alone: primes in all forward intervals. -/
theorem primesAll_of_printed (hin : BHPPrintedCount) :
    ∃ T : ℝ, PrimesAll 0.525 T := by
  obtain ⟨T, hT, hC⟩ := hin
  refine ⟨T, ?_⟩
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le hT hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hnonneg : (0 : ℝ) ≤ (9 / 100 : ℝ) * x ^ (0.525 : ℝ) / Real.log x := by
    positivity
  have hcard : 0 < (primeInterval x (x + x ^ (0.525 : ℝ))).card := by
    exact_mod_cast lt_of_le_of_lt hnonneg (hC x hx)
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  obtain ⟨hpl, hpr, hpp⟩ := mem_primeInterval.mp hp
  exact ⟨p, hpp, hpl, hpr⟩

/-- CONDITIONAL ON the printed BHP count alone, without a half-plane hypothesis. -/
theorem goldbach_short_bhp_of_printed (hin : BHPPrintedCount) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + x ^ (0.525 : ℝ) := by
  obtain ⟨T, hP⟩ := primesAll_of_printed hin
  exact ⟨max (T + 3) 7, goldbach_of_primesAll (by norm_num) hP⟩

/-- The folder's exponent 7/8 follows from the stronger printed BHP count alone. -/
theorem goldbach_short_78_of_printed (hin : BHPPrintedCount) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + x ^ (7 / 8 : ℝ) := by
  obtain ⟨X, hX⟩ := goldbach_short_bhp_of_printed hin
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨n, hn, hnx, hupper⟩ := hX x hxX
  have hpow := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (0.525 : ℝ) ≤ 7 / 8)
  exact ⟨n, hn, hnx, by linarith⟩

/-- The faithful Li consequence now takes the printed BHP count in place of a window input. -/
theorem goldbach_short_bhp_li_eps_of_printed (hin : BHPPrintedCount) :
    ∃ x₀ : ℝ, ∀ {y₀ ε : ℝ}, 0 ≤ ε → ε ≤ 1 / 2 → LiAlmostAllCountEps ε y₀ →
      ∀ x : ℕ, x₀ ≤ x → y₀ ≤ (x : ℝ) ^ (0.525 : ℝ) → 3 ≤ (x : ℝ) ^ (0.525 : ℝ) →
      1 < (9 / 1600 : ℝ) * (0.525 : ℝ) ^ 2 * Real.log x →
      2 * ⌈(x : ℝ) ^ (0.525 : ℝ)⌉₊ + 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧
        (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (21 / 860 + 0.525 * ε : ℝ) := by
  obtain ⟨x₀, hW⟩ := bhpWindowCount_of_printed hin
  refine ⟨x₀, ?_⟩
  intro y₀ ε hε0 hε1 hA x h0 h1 h2 h3 h4
  exact goldbach_short_bhp_li_eps (by norm_num) hε0 hε1 hW hA h0 h1 h2 h3 h4

/-- CONDITIONAL ON the printed BHP count and the faithful Li count.
No elementary side conditions remain. -/
theorem goldbach_short_bhp_li_eps_eventually (hin : BHPPrintedCount) {ε y₀ : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (hA : LiAlmostAllCountEps ε y₀) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧
        (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (21 / 860 + 0.525 * ε : ℝ) := by
  obtain ⟨x₀, hW⟩ := bhpWindowCount_of_printed hin
  have hb0 : (0 : ℝ) ≤ 1 / 21.5 + ε := by positivity
  have hb1 : (1 : ℝ) / 21.5 + ε ≤ 1 := by linarith
  obtain ⟨X, hX⟩ := goldbach_short_b_eventually
    (by norm_num : (0 : ℝ) < 0.525) (by norm_num : (0.525 : ℝ) < 1)
    hb0 hb1 (by norm_num : (0 : ℝ) < 9 / 1600) hW hA
  refine ⟨X, ?_⟩
  intro x hx
  obtain ⟨n, hn, hnx, hupper⟩ := hX x hx
  have heq : (0.525 : ℝ) * (1 / 21.5 + ε) = 21 / 860 + 0.525 * ε := by ring
  exact ⟨n, hn, hnx, by simpa only [heq] using hupper⟩

/-- The standard positive-epsilon consequence, conditional on the two cited printed counts. -/
theorem goldbach_short_of_printed_counts (hBHP : BHPPrintedCount)
    (hLi : LiPrintedExceptionalCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧
        (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (21 / 860 + ε : ℝ) := by
  let η : ℝ := min ε (1 / 2)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  obtain ⟨y₀, hA⟩ := liAlmostAllCountEps_of_printed hLi hη
  obtain ⟨X, hX⟩ := goldbach_short_bhp_li_eps_eventually hBHP hη.le hη1 hA
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hxX : X ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨n, hn, hnx, hupper⟩ := hX x hxX
  have he : (21 / 860 : ℝ) + 0.525 * η ≤ 21 / 860 + ε := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hx1 he
  exact ⟨n, hn, hnx, by linarith⟩

/-- BHP supplies the existing route-a prime input without using the half-plane assumption. -/
theorem explicitShort78_of_printed (hin : BHPPrintedCount) : ExplicitShort78 := by
  intro _ ε hε
  obtain ⟨T, hP⟩ := primesAll_of_printed hin
  refine ⟨max T 1, ?_⟩
  intro x hx
  have hxT : T ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨p, hp, hpl, hpu⟩ := hP x hxT
  have hpow := Real.rpow_le_rpow_of_exponent_le hx1
    (show (0.525 : ℝ) ≤ 7 / 8 + ε by linarith)
  exact ⟨p, hp, hpl, by linarith⟩

/-- BHP Theorem 1 on p. 532 follows from the printed forward count on p. 562. -/
theorem bhp_backward_prime_of_printed (hin : BHPPrintedCount) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∃ p : ℕ,
      p.Prime ∧ x - x ^ (0.525 : ℝ) < p ∧ (p : ℝ) ≤ x := by
  obtain ⟨T, hP⟩ := primesAll_of_printed hin
  obtain ⟨A, hA⟩ := eventually_rpow_le_mul
    (by norm_num : (0.525 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨max A (max (2 * max T 1) 1), ?_⟩
  intro x hx
  have hxA : A ≤ x := by grind
  have hxT : 2 * max T 1 ≤ x := by grind
  have hx1 : 1 ≤ x := by grind
  have hsmall := hA x hxA
  have hpow0 : 0 ≤ x ^ (0.525 : ℝ) := Real.rpow_nonneg (by linarith) _
  have htT : T ≤ x - x ^ (0.525 : ℝ) := by have := le_max_left T 1; linarith
  have ht0 : 0 ≤ x - x ^ (0.525 : ℝ) := by linarith
  obtain ⟨p, hp, hpl, hpu⟩ := hP (x - x ^ (0.525 : ℝ)) htT
  have hpow := Real.rpow_le_rpow ht0 (show x - x ^ (0.525 : ℝ) ≤ x by linarith)
    (by norm_num : (0 : ℝ) ≤ 0.525)
  exact ⟨p, hp, hpl, by linarith⟩

end LeanLab.GoldbachShort78
