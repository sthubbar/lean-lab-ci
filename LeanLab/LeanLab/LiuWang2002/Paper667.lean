import LeanLab.LiuWang2002.Arcs109

/-!
Liu and Wang Lemma 5.1 on page 156, with the named sums and arcs of pages 144 and 145.
The analytic bound is a cited statement. No proof of that bound is asserted here.
The domain lemmas are elementary and do not assume the cited statement.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task667
open Real Set Arcs109

/-- CITED. Lemma 5.1 on page 156, using S from display 3.8 and M2 from display 3.5.
The exponential threshold is equivalent to the printed logarithm threshold on this domain. -/
def M2Bound667 : Prop :=
  ∀ N : ℕ, exp 3100 ≤ (N : ℝ) → ∀ α : ℝ, α ∈ major2 N →
    ‖Vaughan109.S N 0.001 α‖ ≤ 0.4012 * N / Real.log N

/-- A nonempty M2 domain at every allowed natural N.
The upper endpoint of the arc centered at one lies beyond every M1 arc. -/
theorem m2_right_endpoint (N : ℕ) (hN : exp 3100 ≤ (N : ℝ)) :
    (1 + 1 / Q N) ∈ major2 N := by
  classical
  have hN0 : (0 : ℝ) < N := (exp_pos 3100).trans_le hN
  have hL : 3100 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hN
  have hL0 : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hP : (1 : ℝ) ≤ Real.log N ^ 3 := one_le_pow₀ hL1
  have hQ0 : 0 < Q N := div_pos hN0 (pow_pos hL0 7)
  have hr : 0 < 1 / Q N := by positivity
  have hsmall : ∀ q : ℕ, 1 ≤ q → delta N q < 1 / Q N := by
    intro q hq
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hpiq : (3 : ℝ) ≤ Real.pi * q := by
      have hh := mul_le_mul_of_nonneg_left hqR Real.pi_pos.le
      nlinarith [Real.pi_gt_three]
    have hden : 30 * (N : ℝ) ≤ 10 * Real.pi * q * N := by
      have hh := mul_le_mul_of_nonneg_right hpiq hN0.le
      nlinarith
    have hp : Real.log N ^ 3 ≤ Real.log N ^ 7 := pow_le_pow_right₀ hL1 (by norm_num)
    have hn : 0.112 * Real.log N ^ 3 < Real.log N ^ 7 := by
      nlinarith [pow_pos hL0 3]
    calc
      delta N q = 3.36 * Real.log N ^ 3 / (10 * Real.pi * q * N) := rfl
      _ ≤ 3.36 * Real.log N ^ 3 / (30 * N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (0.112 * Real.log N ^ 3) / N := by field_simp [hN0.ne']; ring
      _ < (Real.log N ^ 7) / N := div_lt_div_of_pos_right hn hN0
      _ = 1 / Q N := by simp only [Q, one_div_div]
  change (1 + 1 / Q N) ∈ fareySmall N ∧ (1 + 1 / Q N) ∉ major1 N
  constructor
  · unfold fareySmall
    refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨1, ?_⟩⟩
    have hc : 1 ≤ (1 : ℕ) ∧ ((1 : ℕ) : ℝ) ≤ Real.log N ^ 3 ∧
        1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ Nat.Coprime 1 1 :=
      ⟨by decide, by simpa only [Nat.cast_one] using hP, by decide, by decide, by decide⟩
    rw [if_pos hc]
    simp only [rationalArc, Nat.cast_one, div_one, one_mul, Set.mem_Icc]
    exact ⟨by linarith, le_rfl⟩
  · intro hmem
    unfold major1 at hmem
    rcases Set.mem_iUnion.mp hmem with ⟨q, hq⟩
    rcases Set.mem_iUnion.mp hq with ⟨a, ha⟩
    split_ifs at ha with hc
    · rcases hc with ⟨hq1, hqP, ha1, haq, hcop⟩
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hfrac : (a : ℝ) / q ≤ 1 := by
        apply (div_le_iff₀ hqpos).mpr
        simpa using (Nat.cast_le.mpr haq : (a : ℝ) ≤ q)
      have htop : 1 + 1 / Q N ≤ (a : ℝ) / q + delta N q := ha.2
      have hd := hsmall q hq1
      linarith
    · simp at ha

/-- A concrete natural input and phase satisfying the full Lemma 5.1 domain. -/
theorem m2_domain_instance : ∃ N : ℕ, exp 3100 ≤ (N : ℝ) ∧
    (1 + 1 / Q N) ∈ major2 N := by
  exact ⟨⌈exp 3100⌉₊, Nat.le_ceil _, m2_right_endpoint _ (Nat.le_ceil _)⟩

end LeanLab.LiuWang2002.Task667
#print axioms LeanLab.LiuWang2002.Task667.m2_right_endpoint
#print axioms LeanLab.LiuWang2002.Task667.m2_domain_instance
