/-
AI wrote this Lean code for CODEX task03.
P0074 page 7, Lemma 3.1. The full uniform estimate is an explicit input.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Ramanujan

namespace LeanLab.Grimmelt2019.MainTerm
attribute [local instance] Classical.propDecidable

/-- The integer points in the closed real interval from t minus H to t. -/
noncomputable def shortInterval (t H : ℝ) : Finset ℤ := Finset.Icc ⌈t - H⌉ ⌊t⌋

/-- The full two-branch uniform estimate of Lemma 3.1, stated and not asserted. -/
def Lemma31 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q q : ℕ) (r : ℤ) (H t : ℝ),
    0 < Q → 0 < q → Int.gcd r q = 1 → 0 < H → H < t →
    ‖(∑ n ∈ shortInterval t H, (LamQ Q n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)) -
      (if q ≤ Q then ((ArithmeticFunction.moebius q : ℝ) * H / q.totient : ℂ) else 0)‖ ≤
      C * (if q ≤ Q then (Q : ℝ) ^ 3 else (q : ℝ) * Q + (Q : ℝ) ^ 3)

/-- At truncation one the model is identically one. -/
theorem LamQ_one (n : ℤ) : LamQ 1 n = 1 := by
  norm_num [LamQ, ram, Finset.sum_range_succ]

/-- The cardinality of a closed real interval differs from its length by at most one. -/
theorem shortInterval_card_error {t H : ℝ} (hH : 0 ≤ H) :
    |((shortInterval t H).card : ℝ) - H| ≤ 1 := by
  rw [shortInterval, Int.card_Icc]
  have hfloor := Int.floor_le t
  have hfloor' := Int.lt_floor_add_one t
  have hceil := Int.le_ceil (t - H)
  have hceil' := Int.ceil_lt_add_one (t - H)
  have hab : ⌈t - H⌉ ≤ ⌊t⌋ + 1 := by
    apply Int.ceil_le.mpr
    push_cast
    linarith
  have hd : 0 ≤ ⌊t⌋ + 1 - ⌈t - H⌉ := sub_nonneg.mpr hab
  have hcast : (((⌊t⌋ + 1 - ⌈t - H⌉).toNat : ℕ) : ℝ) =
      (⌊t⌋ : ℝ) + 1 - (⌈t - H⌉ : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hd]
    push_cast
    rfl
  rw [hcast, abs_le]
  constructor <;> linarith

/-- The modulus one and truncation one family of Lemma 3.1 has error at most one. -/
theorem lemma31_one {H t : ℝ} (hH : 0 ≤ H) (r : ℤ) :
    ‖(∑ n ∈ shortInterval t H, (LamQ 1 n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / (1 : ℕ))) - (H : ℂ)‖ ≤ 1 := by
  have he : ∀ n : ℤ, LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / (1 : ℕ)) = 1 := by
    intro n
    simpa only [Nat.cast_one, div_one, Int.cast_mul] using
      LeanLab.PNTPort.LargeSieve.e_int (r * n)
  simp only [LamQ_one, Complex.ofReal_one, he, mul_one, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact shortInterval_card_error hH

/-- The elementary geometric bound on the exact closed interval in Lemma 3.1. -/
theorem shortInterval_exp_sum_le (t H θ : ℝ)
    (hθ : 0 < LeanLab.PNTPort.LargeSieve.dist0 θ) :
    ‖∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * θ)‖ ≤
      1 / (2 * LeanLab.PNTPort.LargeSieve.dist0 θ) := by
  let a : ℤ := ⌈t - H⌉
  let b : ℤ := ⌊t⌋
  have heq : (∑ n ∈ Finset.Icc a b, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * θ)) =
      LeanLab.PNTPort.LargeSieve.e ((a : ℝ) * θ) *
        ∑ k ∈ Finset.range ((b + 1 - a).toNat),
          LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun n : ℤ => (n - a).toNat)
      (fun k : ℕ => a + k) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    · intro k hk
      simp
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [← LeanLab.PNTPort.LargeSieve.e_add]
      congr 1
      have hncast : ((n - a).toNat : ℝ) = (n : ℝ) - a := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_sub]
      rw [hncast]
      ring
  change ‖∑ n ∈ Finset.Icc a b, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * θ)‖ ≤ _
  rw [heq, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
  exact LeanLab.PNTPort.LargeSieve.norm_geom_le _ hθ

#print axioms shortInterval_exp_sum_le
#print axioms LamQ_one
#print axioms shortInterval_card_error
#print axioms lemma31_one
end LeanLab.Grimmelt2019.MainTerm
