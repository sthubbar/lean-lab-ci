/-
Li and Liu, https://arxiv.org/pdf/2610.15784, page 6, Proposition 3.2 and display 21.
The finite primitive residue matrices are real symmetric Gram matrices.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Task37Display64

namespace LeanLab.Linnik.Task37Gram
open Finset
open LeanLab.Linnik.Task37Fourier
open LeanLab.Linnik.U1447Display30 (normSq_sum3)

noncomputable def AqC (q : ℕ) [NeZero q] (i j : Fin 3) : ℂ :=
  (1 / (Nat.totient q : ℂ) ^ 2) * ∑ a : (ZMod q)ˣ,
    zq q (a : ZMod q) ^ ((i : ℕ) + 1) *
      (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((j : ℕ) + 1))

noncomputable def Aq (q : ℕ) [NeZero q] (i j : Fin 3) : ℝ := (AqC q i j).re

lemma zq_neg {q : ℕ} [NeZero q] (a : ZMod q) :
    zq q (-a) = (starRingEnd ℂ) (zq q a) := by
  unfold zq
  rw [map_mul, map_div₀, map_one, map_natCast, map_sum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [char_star]
  congr 1
  ring

lemma AqC_conj {q : ℕ} [NeZero q] (i j : Fin 3) :
    (starRingEnd ℂ) (AqC q i j) = AqC q i j := by
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ :=
    ⟨fun a => -a, fun a => -a, neg_neg, neg_neg⟩
  have he : (∑ a : (ZMod q)ˣ, zq q (a : ZMod q) ^ ((i : ℕ) + 1) *
      (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((j : ℕ) + 1))) =
      ∑ a : (ZMod q)ˣ, (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((i : ℕ) + 1) *
      (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((j : ℕ) + 1))) := by
    rw [← e.sum_comp (fun a : (ZMod q)ˣ => zq q (a : ZMod q) ^ ((i : ℕ) + 1) *
      (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((j : ℕ) + 1)))]
    refine sum_congr rfl fun a _ => ?_
    simp only [e, Equiv.coe_fn_mk, Units.val_neg, zq_neg, map_mul, map_pow]
  unfold AqC
  rw [map_mul, map_div₀, map_one, map_pow, map_natCast, map_sum]
  rw [he]

lemma AqC_hermitian {q : ℕ} [NeZero q] (i j : Fin 3) :
    (starRingEnd ℂ) (AqC q i j) = AqC q j i := by
  unfold AqC
  rw [map_mul, map_div₀, map_one, map_pow, map_natCast, map_sum]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

/-- The complex primitive residue sum is real. -/
theorem AqC_eq_real {q : ℕ} [NeZero q] (i j : Fin 3) : AqC q i j = (Aq q i j : ℂ) := by
  have hi := congrArg Complex.im (AqC_conj (q := q) i j)
  simp only [Complex.conj_im] at hi
  have hz : (AqC q i j).im = 0 := by linarith
  apply Complex.ext
  · rfl
  · simpa using hz

/-- The finite matrices in display 21 are symmetric. -/
theorem Aq_symm {q : ℕ} [NeZero q] (i j : Fin 3) : Aq q i j = Aq q j i := by
  have he := (AqC_conj (q := q) i j).symm.trans (AqC_hermitian (q := q) i j)
  exact congrArg Complex.re he

lemma Aq_expand {q : ℕ} [NeZero q] (i j : Fin 3) :
    Aq q i j = (1 / (Nat.totient q : ℝ) ^ 2) * ∑ a : (ZMod q)ˣ,
      (zq q (a : ZMod q) ^ ((i : ℕ) + 1) *
        (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((j : ℕ) + 1))).re := by
  have hw : (1 / (Nat.totient q : ℂ) ^ 2) = ((1 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  unfold Aq AqC
  rw [hw, Complex.re_ofReal_mul, Complex.re_sum]

/-- The finite quadratic form equals a sum of squared norms. -/
theorem Aq_gram {q : ℕ} [NeZero q] (x : Fin 3 → ℝ) :
    (∑ i, ∑ j, x i * Aq q i j * x j) =
      (1 / (Nat.totient q : ℝ) ^ 2) * ∑ a : (ZMod q)ˣ,
        ‖∑ i, (x i : ℂ) * zq q (a : ZMod q) ^ ((i : ℕ) + 1)‖ ^ 2 := by
  simp_rw [Aq_expand]
  calc
    _ = (1 / (Nat.totient q : ℝ) ^ 2) * ∑ i, ∑ j, ∑ a : (ZMod q)ˣ,
        x i * x j * (zq q (a : ZMod q) ^ ((i : ℕ) + 1) *
          (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((j : ℕ) + 1))).re := by
      simp only [mul_sum, sum_mul]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun a _ => ?_
      ring
    _ = (1 / (Nat.totient q : ℝ) ^ 2) * ∑ a : (ZMod q)ˣ, ∑ i, ∑ j,
        x i * x j * (zq q (a : ZMod q) ^ ((i : ℕ) + 1) *
          (starRingEnd ℂ) (zq q (a : ZMod q) ^ ((j : ℕ) + 1))).re := by
      congr 1
      rw [sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
    _ = _ := by
      congr 1
      refine sum_congr rfl fun a _ => ?_
      symm
      exact normSq_sum3 x (fun i => zq q (a : ZMod q) ^ ((i : ℕ) + 1))

/-- Every finite primitive residue matrix is positive semidefinite. -/
theorem Aq_psd {q : ℕ} [NeZero q] (x : Fin 3 → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * Aq q i j * x j := by
  rw [Aq_gram]
  exact mul_nonneg (by positivity) (sum_nonneg fun a _ => sq_nonneg _)

/-- The first nontrivial odd modulus supplies an instance of both matrix properties. -/
theorem gram_instance : Aq 3 0 1 = Aq 3 1 0 ∧
    0 ≤ ∑ i, ∑ j, (![1, -1, 1] i : ℝ) * Aq 3 i j * ![1, -1, 1] j :=
  ⟨Aq_symm 0 1, Aq_psd ![1, -1, 1]⟩

end LeanLab.Linnik.Task37Gram

#print axioms LeanLab.Linnik.Task37Gram.zq_neg
#print axioms LeanLab.Linnik.Task37Gram.AqC_conj
#print axioms LeanLab.Linnik.Task37Gram.AqC_hermitian
#print axioms LeanLab.Linnik.Task37Gram.AqC_eq_real
#print axioms LeanLab.Linnik.Task37Gram.Aq_symm
#print axioms LeanLab.Linnik.Task37Gram.Aq_expand
#print axioms LeanLab.Linnik.Task37Gram.Aq_gram
#print axioms LeanLab.Linnik.Task37Gram.Aq_psd
#print axioms LeanLab.Linnik.Task37Gram.gram_instance
