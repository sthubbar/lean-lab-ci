import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
Unit P1122-0007, burst 20261122, step singser-settle. Settles the FALSE QUESTION that burst
prove-20261117 left on `leaf_singular_series_coefficients481` of
`SPLIT_pintz_explicit_formula481.lean`.

The leaf is FALSE as written. It quantifies over every indexed family `z`, including families
whose index zero entry does not have conductor one. The first clause forces `Sg 0 0 n = 𝔖(n)`
and the third clause forces `‖Sg 0 0 n‖ ≤ ε` for every small `ε` as soon as the conductor of
`z 0` fails to divide `Cε ε * n`. With conductor `3` and `n = 2` this needs `𝔖(2) ≤ ε` for all
small `ε`, while `𝔖(2) ≥ 1/2`. P0045 journal page 775, Lemma 4.1, attaches the coefficients to
the actual zero family, whose index zero entry is the pole with conductor one, so the paper
does not claim the leaf.

The missing piece on 11-17 was a lower bound for the infinite product `Sing 2` of
`Statements.lean`, page 2 of P0045. `half_le_Sing_two` supplies it without deciding
convergence: a product that is not multipliable has value one by convention, and a multipliable
one is a limit of finite products, each at least `1/2` by the telescoping product of
`1 - 1/(m-1)^2`.

Nothing in `SPLIT_pintz_explicit_formula481.lean` is used or changed. AI wrote the Lean code.
Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- Auxiliary minorant for the local factors of `Sing 2`, P0045 page 2 display for `𝔖(n)`:
one for `m ≤ 2`, and the factor `1 - 1/(m-1)^2` of a prime not dividing `n` otherwise. -/
def singMinor1122 (m : ℕ) : ℝ := if m ≤ 2 then 1 else 1 - 1 / ((m : ℝ) - 1) ^ 2

/-- The minorant is positive. -/
theorem singMinor1122_pos (m : ℕ) : 0 < singMinor1122 m := by
  unfold singMinor1122
  split_ifs with h
  · exact one_pos
  · have hm : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
    have h1 : (1 : ℝ) < ((m : ℝ) - 1) ^ 2 := by nlinarith
    have h2 : 1 / ((m : ℝ) - 1) ^ 2 < 1 := by
      rw [div_lt_one (by linarith)]
      exact h1
    linarith

/-- The minorant is at most one. -/
theorem singMinor1122_le_one (m : ℕ) : singMinor1122 m ≤ 1 := by
  unfold singMinor1122
  split_ifs with h
  · exact le_rfl
  · have : 0 ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
    linarith

/-- Telescoping: the product of the minorant over `m < N + 3` is `(N + 2) / (2 (N + 1))`. -/
theorem prod_singMinor1122_range (N : ℕ) :
    ∏ m ∈ range (N + 3), singMinor1122 m = ((N : ℝ) + 2) / (2 * ((N : ℝ) + 1)) := by
  induction N with
  | zero =>
    have h0 : singMinor1122 0 = 1 := by simp [singMinor1122]
    have h1 : singMinor1122 1 = 1 := by simp [singMinor1122]
    have h2 : singMinor1122 2 = 1 := by simp [singMinor1122]
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_zero, h0, h1, h2]
    norm_num
  | succ N ih =>
    rw [show N + 1 + 3 = (N + 3) + 1 from rfl, Finset.prod_range_succ, ih]
    have hstep : singMinor1122 (N + 3) = 1 - 1 / (((N + 3 : ℕ) : ℝ) - 1) ^ 2 := by
      unfold singMinor1122
      rw [if_neg (by omega)]
    rw [hstep]
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    push_cast
    have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N : ℝ) + 3 - 1) ≠ 0 := by
      have : (0 : ℝ) < (N : ℝ) + 3 - 1 := by linarith
      exact this.ne'
    have h3 : ((N : ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- Every finite product of the minorant is at least `1/2`. -/
theorem half_le_prod_singMinor1122 (t : Finset ℕ) : (1 : ℝ) / 2 ≤ ∏ m ∈ t, singMinor1122 m := by
  have hsub : t ⊆ range (t.sup id + 3) := by
    intro m hm
    have : m ≤ t.sup id := Finset.le_sup (f := id) hm
    exact Finset.mem_range.2 (by omega)
  have hsplit := Finset.prod_sdiff (f := singMinor1122) hsub
  have hrest : ∏ m ∈ range (t.sup id + 3) \ t, singMinor1122 m ≤ 1 :=
    (Finset.prod_induction singMinor1122 (fun x : ℝ => 0 ≤ x ∧ x ≤ 1)
      (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩)
      ⟨zero_le_one, le_rfl⟩
      (fun m _ => ⟨(singMinor1122_pos m).le, singMinor1122_le_one m⟩)).2
  have ht : 0 ≤ ∏ m ∈ t, singMinor1122 m :=
    Finset.prod_nonneg (fun m _ => (singMinor1122_pos m).le)
  have hfull := prod_singMinor1122_range (t.sup id)
  have hN : (0 : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlow : (1 : ℝ) / 2 ≤ (((t.sup id : ℕ) : ℝ) + 2) / (2 * (((t.sup id : ℕ) : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  calc (1 : ℝ) / 2 ≤ ∏ m ∈ range (t.sup id + 3), singMinor1122 m := by rw [hfull]; exact hlow
    _ = (∏ m ∈ range (t.sup id + 3) \ t, singMinor1122 m) * ∏ m ∈ t, singMinor1122 m :=
        hsplit.symm
    _ ≤ 1 * ∏ m ∈ t, singMinor1122 m := mul_le_mul_of_nonneg_right hrest ht
    _ = ∏ m ∈ t, singMinor1122 m := one_mul _

/-- The local factor of `Sing 2` at a prime, P0045 page 2, dominates the minorant. -/
theorem singMinor1122_le_factor (p : {p : ℕ // p.Prime}) :
    singMinor1122 p.1 ≤
      (if p.1 ∣ 2 then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
  have hp2 : 2 ≤ p.1 := p.2.two_le
  by_cases hd : p.1 ∣ 2
  · have hle : p.1 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have he : p.1 = 2 := le_antisymm hle hp2
    rw [if_pos hd]
    unfold singMinor1122
    rw [if_pos hle, he]
    norm_num
  · have hgt : ¬ p.1 ≤ 2 := by
      intro hle
      have he : p.1 = 2 := le_antisymm hle hp2
      exact hd (by rw [he])
    rw [if_neg hd]
    unfold singMinor1122
    rw [if_neg hgt]

/-- Every finite partial product of the Euler product `Sing 2` is at least `1/2`. -/
theorem half_le_partial_Sing_two (s : Finset {p : ℕ // p.Prime}) :
    (1 : ℝ) / 2 ≤ ∏ p ∈ s,
      (if p.1 ∣ 2 then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
  have h1 : ∏ p ∈ s, singMinor1122 p.1 ≤ ∏ p ∈ s,
      (if p.1 ∣ 2 then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact mul_le_mul (singMinor1122_le_factor a) ih
        (Finset.prod_nonneg (fun p _ => (singMinor1122_pos p.1).le))
        (le_trans (singMinor1122_pos a.1).le (singMinor1122_le_factor a))
  have h2 : ∏ p ∈ s, singMinor1122 p.1 = ∏ m ∈ s.image Subtype.val, singMinor1122 m := by
    rw [Finset.prod_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  have h3 := half_le_prod_singMinor1122 (s.image Subtype.val)
  linarith

/-- P0045 page 2, the singular series at `n = 2`: `𝔖(2) ≥ 1/2`. The true value is twice the twin
prime constant, about `1.32`; only a positive lower bound is needed here. No convergence is
decided: a product that is not multipliable is one by convention. -/
theorem half_le_Sing_two : (1 : ℝ) / 2 ≤ Sing 2 := by
  unfold Sing
  by_cases hm : Multipliable (fun p : {p : ℕ // p.Prime} =>
      if p.1 ∣ 2 then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2)
  · exact ge_of_tendsto' hm.hasProd (fun s => half_le_partial_Sing_two s)
  · rw [tprod_eq_one_of_not_multipliable hm]
    norm_num

/-- `2` lies in `evenJ131 2`: it is in `[1, 2]`, even, and `2 * 2 / 3 ≤ 2`. Restated here so that
this file does not import `DecompF728`. -/
theorem two_mem_evenJ131_two1122 : (2 : ℕ) ∈ evenJ131 2 := by
  unfold evenJ131
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨by norm_num, le_refl 2⟩, by decide, by norm_num⟩

/-- FALSE flag. The statement of `leaf_singular_series_coefficients481` of
`SPLIT_pintz_explicit_formula481.lean`, word for word with its parameters universally
quantified, is false. Witness: `ε₀ = 1`, `Cε` constantly `1`, `X = 2`, `K = 0`, the one entry of
`z` has conductor `3`, `ε = 1/4`, `i = j = 0`, `n = 2`. Then `3 ∤ 1 * 2`, so the third clause
gives `‖Sg 0 0 2‖ ≤ 1/4`, while the first clause gives `Sg 0 0 2 = 𝔖(2) ≥ 1/2`. The paper,
P0045 journal page 775 Lemma 4.1, only speaks of the actual zero family, whose index zero entry
is the pole of conductor one. -/
theorem leaf_singular_series_coefficients481_false :
    ¬ (∀ (ε₀ : ℝ) (_hε₀ : 0 < ε₀) (Cε : ℝ → ℕ) (_hC : ∀ ε, 0 < Cε ε),
        ∀ (X K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          ∃ Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ,
            (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
            (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) ∧
            (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
              (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε)) := by
  intro h
  obtain ⟨Sg, h1, -, h3⟩ := h 1 one_pos (fun _ => 1) (fun _ => Nat.one_pos) 2 0
    (fun _ => ⟨3, (1, 0)⟩)
  have hdvd : ¬ (3 : ℕ) ∣ 1 * 2 := by decide
  have hsmall := h3 (1 / 4) (by norm_num) (by norm_num) 0 0 2 two_mem_evenJ131_two1122
    (Or.inl hdvd)
  rw [h1 2 two_mem_evenJ131_two1122, Complex.norm_real, Real.norm_eq_abs] at hsmall
  have hS := half_le_Sing_two
  have habs : Sing 2 ≤ |Sing 2| := le_abs_self _
  linarith

/-- The repaired form is true and carries no content of the paper: when the index zero entry has
conductor one, as in P0045 journal page 775 Lemma 4.1, and `𝔖` is nonnegative on `evenJ131 X`,
the coefficients that vanish off the pole pair satisfy all three clauses. This is why the
coefficient step cannot be split from the estimate step of Lemma 4.1. -/
theorem singular_series_coefficients_pole_one1122 (ε₀ : ℝ) (Cε : ℝ → ℕ) (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ) (hz : (z 0).1 = 1)
    (hS : ∀ n ∈ evenJ131 X, 0 ≤ Sing n) :
    ∃ Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ,
      (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
      (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) ∧
      (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
        (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by
  refine ⟨fun i j n => if i = 0 ∧ j = 0 then (Sing n : ℂ) else 0, ?_, ?_, ?_⟩
  · intro n _
    simp
  · intro i j n hn
    by_cases hij : i = 0 ∧ j = 0
    · simp only [hij, and_self, if_true, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_of_nonneg (hS n hn)).le
    · simp only [hij, if_false, norm_zero]
      exact hS n hn
  · intro ε hε _ i j n _ hnd
    by_cases hij : i = 0 ∧ j = 0
    · exfalso
      rcases hnd with hi | hj
      · rw [hij.1, hz] at hi
        exact hi (one_dvd _)
      · rw [hij.2, hz] at hj
        exact hj (one_dvd _)
    · simp only [hij, if_false, norm_zero]
      exact hε.le

end
end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.half_le_Sing_two
#print axioms LeanLab.LPZ2007.two_mem_evenJ131_two1122
#print axioms LeanLab.LPZ2007.leaf_singular_series_coefficients481_false
#print axioms LeanLab.LPZ2007.singular_series_coefficients_pole_one1122
