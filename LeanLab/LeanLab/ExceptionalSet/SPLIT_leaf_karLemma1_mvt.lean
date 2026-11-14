/-
Split of the sealed statement `leaf_karLemma1_mvt` of
`LeanLab.ExceptionalSet.KaracubaSplit`, that is the proposition `KarLemma1`, into the mean
value bound at the least admissible exponent together with the two steps that carry it to
every larger admissible exponent.

The target statement is unchanged: it is the assembly `leaf_karLemma1_mvt_split` at the end
of this file, proved from the leaves below.
AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Helper lemmas -/

/-- The exponential `eC` is continuous. -/
private theorem continuous_eC : Continuous eC := by
  unfold eC
  fun_prop

/-- The box `[0,1]^n` is compact. -/
private theorem isCompact_box (n : ℕ) :
    IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

/-- The exponential sum is a continuous function of the coefficients. -/
private theorem continuous_expSum (n P : ℕ) :
    Continuous fun α : Fin n → ℝ =>
      ∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1)) := by
  refine continuous_finsetSum _ (fun x _ => ?_)
  refine continuous_eC.comp ?_
  refine continuous_finsetSum _ (fun j _ => ?_)
  exact (continuous_apply j).mul continuous_const

/-- Every summand has modulus one, so the sum has modulus at most `P`. -/
private theorem norm_expSum_le (n P : ℕ) (hP : 1 ≤ P) (α : Fin n → ℝ) :
    ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ≤ (P : ℝ) := by
  calc ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖
      ≤ ∑ x ∈ Finset.Icc 1 P, ‖eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ :=
        norm_sum_le _ _
    _ = ∑ x ∈ Finset.Icc 1 P, (1 : ℝ) :=
        Finset.sum_congr rfl (fun x _ => norm_eC _)
    _ = (P : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]

/-! ### Leaves -/

/-- LEAF. The mean value bound at the least admissible exponent `b = n l + [n(n+1)/4 + 1]`
of the target: on the unit cube, the integral of the `2b`-th power of the exponential sum in
`n` coefficients is below `(20 n)^((n(n+1)/2) l)` times the power of `P` belonging to that
exponent. One inequality, and the case `b = b_l` of the target; every larger admissible `b`
is reached from it by `leaf_integral_step` and `leaf_rpow_step_identity`. -/
theorem leaf_mvt_threshold :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  sorry

/-- LEAF. One step in the exponent: every summand of the exponential sum has modulus one,
so the sum has modulus at most `P` everywhere on the cube, hence raising the power from `2b`
to `2b + 2` multiplies the integral by at most `P^2`. One inequality. -/
theorem leaf_integral_step :
    ∀ n : ℕ, 12 ≤ n → ∀ b : ℕ, ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (Nat.succ b) : ℕ) ≤
        (P : ℝ) ^ 2 *
          ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
            ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
              (2 * (b) : ℕ) := by
  intro n _ b P hP
  set s : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) with hs
  set S : (Fin n → ℝ) → ℂ :=
    fun α => ∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1)) with hS
  have hScont : Continuous S := continuous_expSum n P
  have hle : ∀ α : Fin n → ℝ, ‖S α‖ ≤ (P : ℝ) := fun α => norm_expSum_le n P hP α
  have hscomp : IsCompact s := by rw [hs]; exact isCompact_box n
  have hint : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun α : Fin n → ℝ => ‖S α‖ ^ k) s := by
    intro k
    exact ContinuousOn.integrableOn_compact hscomp (hScont.norm.pow k).continuousOn
  have key : ∀ α : Fin n → ℝ, ‖S α‖ ^ (2 * Nat.succ b) ≤ (P : ℝ) ^ 2 * ‖S α‖ ^ (2 * b) := by
    intro α
    have hstep : ‖S α‖ ^ (2 * Nat.succ b) = ‖S α‖ ^ (2 * b) * ‖S α‖ ^ 2 := by
      rw [show 2 * Nat.succ b = 2 * b + 2 from by omega, pow_add]
    have hsq : ‖S α‖ ^ 2 ≤ (P : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hle α) 2
    calc ‖S α‖ ^ (2 * Nat.succ b) = ‖S α‖ ^ (2 * b) * ‖S α‖ ^ 2 := hstep
      _ ≤ ‖S α‖ ^ (2 * b) * (P : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (P : ℝ) ^ 2 * ‖S α‖ ^ (2 * b) := by ring
  calc ∫ α in s, ‖S α‖ ^ (2 * Nat.succ b)
      ≤ ∫ α in s, (P : ℝ) ^ 2 * ‖S α‖ ^ (2 * b) :=
        MeasureTheory.integral_mono (hint (2 * Nat.succ b))
          (MeasureTheory.Integrable.const_mul (hint (2 * b)) _) key
    _ = (P : ℝ) ^ 2 * ∫ α in s, ‖S α‖ ^ (2 * b) := MeasureTheory.integral_const_mul _ _

/-- LEAF. The bookkeeping identity of the induction step: for `P > 0` the right hand side
of the target at the exponent `b + 1` is `P^2` times the right hand side at the exponent `b`,
because the exponent of `P` gains exactly `2` and `P^(u + 2) = P^u * P^2`. One identity. -/
theorem leaf_rpow_step_identity :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ b : ℕ, ∀ P : ℕ, 0 < P →
      (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
      (P : ℝ) ^ ((2 * (Nat.succ b) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
        + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) =
        (P : ℝ) ^ 2 *
          ((20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
          (P : ℝ) ^ ((2 * (b) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
            + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l)) := by
  intro n _ l _ b P hP
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hcast : 2 * ((Nat.succ b : ℕ) : ℝ) = 2 * (b : ℝ) + 2 := by
    have hb : Nat.succ b = b + 1 := rfl
    rw [hb]
    push_cast
    ring
  have hexp : 2 * ((Nat.succ b : ℕ) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
        + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l =
      ((2 * (b : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
        + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l)) + 2 := by
    rw [hcast]
    ring
  have hp2 : (P : ℝ) ^ (2 : ℝ) = (P : ℝ) ^ 2 := by norm_num
  rw [hexp, Real.rpow_add hPpos, hp2]
  ring

/-- PROVED from the three leaves. Induction in the exponent from the admissible
`n l + [n(n+1)/4 + 1]` up to `b`: `leaf_integral_step` bounds the growth of the integral by
`P^2` per step, and `leaf_rpow_step_identity` says the right hand side grows by exactly the
same factor. -/
private theorem karLemma1_of_threshold (n l : ℕ) (hn : 12 ≤ n) (hl : 0 < l)
    (P : ℕ) (hP : 0 < P) :
    ∀ b : ℕ, n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) ≤ b →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (b) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (b) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  intro b hb
  refine Nat.le_induction (m := n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) ?base ?step b hb
  case base =>
    have h := leaf_mvt_threshold n hn l hl P hP
    simpa using h
  case step =>
    intro m hm ih
    have hstep := leaf_integral_step n hn m P hP
    have hid := leaf_rpow_step_identity n hn l hl m P hP
    have hP2 : (0 : ℝ) < (P : ℝ) ^ 2 := pow_pos (by exact_mod_cast hP) 2
    rw [hid]
    exact lt_of_le_of_lt hstep (mul_lt_mul_of_pos_left ih hP2)

/-- The sealed statement of `leaf_karLemma1_mvt`, from the leaves of this file. -/
theorem leaf_karLemma1_mvt_split : KarLemma1 := by
  intro n hn l hl b hb P hP
  exact karLemma1_of_threshold n l hn hl P hP b hb

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
