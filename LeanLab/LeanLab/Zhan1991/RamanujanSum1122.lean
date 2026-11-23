import LeanLab.Zhan1991.SPLIT_major_1122

/-!
P0068 Zhan 1991, page 271, step 2 of SPLIT_major_1122, the sum over the arcs `a mod q`:
`Σ_{(a, q) = 1} e(-aN/q) = c_q(N)`, the real Ramanujan sum `ramanujanC`. PROVED; the sine part
cancels under `a ↦ q - a`. An ingredient of the open LEAF `majorAssembly_of_approx`.
burst-20261122, session S80. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real

/-- The sine part of the Ramanujan sum vanishes, by the involution `a ↦ q - a`. PROVED. -/
theorem ramanujan_sin_zero (q N : ℕ) (hq : 1 ≤ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      Real.sin (2 * π * (a : ℝ) * N / q)) = 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hrefl : ∀ a : ℕ, 0 < a → a < q →
      Real.sin (2 * π * ((q - a : ℕ) : ℝ) * N / q) = -Real.sin (2 * π * (a : ℝ) * N / q) := by
    intro a ha haq
    rw [Nat.cast_sub haq.le]
    have e : 2 * π * ((q : ℝ) - a) * N / q = (N : ℕ) * (2 * π) - 2 * π * a * N / q := by
      field_simp
    rw [e, Real.sin_nat_mul_two_pi_sub]
  apply Finset.sum_involution (fun a _ => (q - a) % q)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q), hrefl a hpos ha.1]; ring
  · intro a ha hne heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp at hne
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q)] at heq
      apply hne
      have h2 : 2 * a = q := by omega
      have e : 2 * π * (a : ℝ) * N / q = (N : ℕ) * π := by
        rw [← h2]; push_cast; field_simp
      rw [e, Real.sin_nat_mul_pi]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simpa using ha.2
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q)]
      exact (Nat.coprime_self_sub_left (by omega)).mpr ha.2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q), Nat.mod_eq_of_lt (by omega)]; omega

/-- Page 271, `Σ_{a mod q, (a, q) = 1} e(-aN/q) = c_q(N)`. PROVED. -/
theorem ramanujan_sum_complex (q N : ℕ) (hq : 1 ≤ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ee (-((a : ℝ) * N / q))) =
      (ramanujanC q N : ℂ) := by
  have he : ∀ a : ℕ, ee (-((a : ℝ) * N / q)) =
      (Real.cos (2 * π * (a : ℝ) * N / q) : ℂ) - (Real.sin (2 * π * (a : ℝ) * N / q) : ℂ) *
        Complex.I := by
    intro a
    unfold ee
    have : (2 * (π : ℂ) * Complex.I * ((-((a : ℝ) * N / q) : ℝ) : ℂ)) =
        ((-(2 * π * (a : ℝ) * N / q) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
    ramanujan_sin_zero q N hq]
  unfold ramanujanC
  simp
