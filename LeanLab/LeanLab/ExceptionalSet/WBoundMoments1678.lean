/-
Finite moment tools for SPLIT_leaf_W_bound, following Karacuba p. 246 before display 5.
The prescribed power-sum count also uses Lemma 1 on p. 243, CONDITIONAL ON KarLemma1.
All sums here are finite. No positivity of a Fourier integrand is assumed.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.KaracubaSplit
import LeanLab.ExceptionalSet.SPLIT_leaf_mvt_threshold

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539
open scoped ComplexConjugate

/-- The even moment is the sum over pairs of tuples of their phase differences. -/
theorem leafW_even_moment_expansion {ι : Type*} [Fintype ι] (φ : ι → ℝ) (k : ℕ) :
    ((‖∑ x : ι, eC (φ x)‖ ^ (2 * k) : ℝ) : ℂ) =
      ∑ u : Fin k → ι, ∑ v : Fin k → ι,
        eC (∑ i : Fin k, (φ (u i) - φ (v i))) := by
  classical
  have hprod (u : Fin k → ι) :
      (∏ i : Fin k, eC (φ (u i))) = eC (∑ i : Fin k, φ (u i)) := by
    simp [eC, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  calc
    ((‖∑ x : ι, eC (φ x)‖ ^ (2 * k) : ℝ) : ℂ) =
        ((∑ x : ι, eC (φ x)) * conj (∑ x : ι, eC (φ x))) ^ k := by
      rw [Complex.mul_conj']
      simp [pow_mul]
    _ = (∑ x : ι, eC (φ x)) ^ k * (∑ x : ι, conj (eC (φ x))) ^ k := by
      rw [mul_pow, map_sum]
    _ = _ := by
      rw [Fintype.sum_pow, Fintype.sum_pow, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      rw [hprod u, ← map_prod, hprod v, ← eC_neg]
      simp only [eC, ← Complex.exp_add, Finset.sum_sub_distrib, Complex.ofReal_sub]
      congr 1
      push_cast
      ring

/-- Expanding a polynomial row cancels the constant phase and separates its power sums. -/
theorem leafW_polynomial_row_moment (n M k y : ℕ) (b : ℝ) (β : ℕ → ℝ) :
    ‖∑ z : Fin (M + 1),
      eC (b + ∑ j ∈ Finset.Icc 1 n, β j * ((y : ℝ) * (z : ℕ)) ^ j)‖ ^ (2 * k) =
      (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        eC (∑ j ∈ Finset.Icc 1 n, β j * (y : ℝ) ^ j *
          ((∑ i : Fin k, ((u i : ℕ) : ℝ) ^ j) -
            ∑ i : Fin k, ((v i : ℕ) : ℝ) ^ j))).re := by
  have h := congrArg Complex.re (leafW_even_moment_expansion
    (fun z : Fin (M + 1) =>
      b + ∑ j ∈ Finset.Icc 1 n, β j * ((y : ℝ) * (z : ℕ)) ^ j) k)
  simp only [Complex.ofReal_re] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  simp only [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, mul_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.mul_sum, mul_sub]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A prescribed difference has at most as many representations as the zero difference.
This is property a of the counting interpretation of J on p. 246. -/
theorem leafW_difference_count_le_zero {ι G : Type*} [Fintype ι] [AddCommGroup G]
    [DecidableEq G] (A : ι → G) (t : G) :
    (∑ x : ι, ∑ y : ι, if A x - A y = t then (1 : ℝ) else 0) ≤
      ∑ x : ι, ∑ y : ι, if A x - A y = 0 then (1 : ℝ) else 0 := by
  classical
  let S := Finset.univ.image A
  let w : G → ℝ := fun a => ((Finset.univ.filter (fun x : ι => A x = a)).card : ℝ)
  have hw (a : G) (ha : a ∉ S) : w a = 0 := by
    have hf : (Finset.univ.filter (fun x : ι => A x = a)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx hxa
      exact ha (Finset.mem_image.mpr ⟨x, hx, hxa⟩)
    simp [w, hf]
  have hgroup (F : G → ℝ) :
      (∑ x : ι, F (A x)) = ∑ a ∈ S, w a * F a := by
    symm
    calc
      ∑ a ∈ S, w a * F a =
          ∑ a ∈ S, ∑ _x ∈ Finset.univ.filter (fun x : ι => A x = a), F a := by
        simp [w]
      _ = _ := Finset.sum_fiberwise_of_maps_to'
        (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) F
  have hform (v : G) :
      (∑ x : ι, ∑ y : ι, if A x - A y = v then (1 : ℝ) else 0) =
        ∑ a ∈ S, w a * w (a - v) := by
    have hinner (x : ι) :
        (∑ y : ι, if A x - A y = v then (1 : ℝ) else 0) = w (A x - v) := by
      simp only [w, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      have heq : A x - A y = v ↔ A y = A x - v := by
        constructor
        · intro h
          apply (eq_sub_iff_add_eq).mpr
          rw [(sub_eq_iff_eq_add).mp h]
          abel
        · intro h
          rw [h]
          abel
      simp [heq]
    simp only [hinner]
    exact hgroup (fun a => w (a - v))
  rw [hform t, hform 0]
  simp only [sub_zero, ← pow_two]
  calc
    ∑ a ∈ S, w a * w (a - t) =
        ∑ a ∈ S.filter (fun a => a + -t ∈ S), w a * w (a + -t) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hat : a + -t ∈ S
      · simp [hat, sub_eq_add_neg]
      · simp [hat, sub_eq_add_neg, hw (a + -t) hat]
    _ ≤ _ := LeanLab.ExceptionalSet.Decomp538a.partial_correlation_le_energy S w (-t)

/-- CONDITIONAL ON KarLemma1. Every prescribed vector of power-sum differences satisfies
the same upper bound as the zero vector, using the proved integral-count identity. -/
theorem leafW_shifted_solution_bound (h1 : KarLemma1) (n l P : ℕ)
    (hn : 12 ≤ n) (hl : 0 < l) (hP : 0 < P) (ξ : Fin n → ℝ) :
    let k := n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊
    (∑ u : Fin k → Fin P, ∑ v : Fin k → Fin P,
      if (∀ j : Fin n,
        (∑ i : Fin k, (((u i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) -
          (∑ i : Fin k, (((v i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) = ξ j)
        then (1 : ℝ) else 0) <
      (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * k : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2 +
          ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  classical
  dsimp only
  let k := n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊
  let A : (Fin k → Fin P) → Fin n → ℝ :=
    fun u j => ∑ i : Fin k, (((u i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
  have hcount := leafW_difference_count_le_zero A ξ
  simp only [funext_iff, Pi.sub_apply, sub_eq_zero] at hcount
  have hid := leaf_integral_eq_solution_count n hn l hl P hP
  have hmean := h1 n hn l hl k le_rfl P hP
  exact lt_of_le_of_lt hcount (hid ▸ hmean)

/-- The first Holder step of p. 246 with each polynomial row expanded exactly. -/
theorem leafW_first_moment_bound (n M k : ℕ) (b : ℝ) (β : ℕ → ℝ) (hk : 0 < k) :
    ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      eC (b + ∑ j ∈ Finset.Icc 1 n, β j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k) ≤
      ((M : ℝ) + 1) ^ (2 * k - 1) *
        ∑ y ∈ Finset.range (M + 1),
          (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
            eC (∑ j ∈ Finset.Icc 1 n, β j * (y : ℝ) ^ j *
              ((∑ i : Fin k, ((u i : ℕ) : ℝ) ^ j) -
                ∑ i : Fin k, ((v i : ℕ) : ℝ) ^ j))).re := by
  have h := LeanLab.ExceptionalSet.Decomp538a.first_holder_step
    (Finset.range (M + 1))
    (fun y => ∑ z ∈ Finset.range (M + 1),
      eC (b + ∑ j ∈ Finset.Icc 1 n, β j * (((y * z : ℕ) : ℝ) ^ j))) k hk
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro y _
  symm
  have hrow := leafW_polynomial_row_moment n M k y b β
  rw [Fin.sum_univ_eq_sum_range (fun z : ℕ =>
    eC (b + ∑ j ∈ Finset.Icc 1 n, β j * ((y : ℝ) * z) ^ j)) (M + 1)] at hrow
  simpa only [Nat.cast_mul] using hrow

/-- Two Holder steps reduce a bilinear sum to moments of its tuple-difference kernels,
before grouping those tuples by their power sums as on p. 246. -/
theorem leafW_two_holder_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (φ : ι → κ → ℝ) (k : ℕ) (hk : 0 < k) :
    ‖∑ y : ι, ∑ z : κ, eC (φ y z)‖ ^ ((2 * k) * (2 * k)) ≤
      (Fintype.card ι : ℝ) ^ ((2 * k - 1) * (2 * k)) *
        (Fintype.card κ : ℝ) ^ ((2 * k) * (2 * k - 1)) *
          ∑ u : Fin k → κ, ∑ v : Fin k → κ,
            ‖∑ y : ι, eC (∑ i : Fin k, (φ y (u i) - φ y (v i)))‖ ^ (2 * k) := by
  classical
  let K : (Fin k → κ) → (Fin k → κ) → ℂ :=
    fun u v => ∑ y : ι, eC (∑ i : Fin k, (φ y (u i) - φ y (v i)))
  have hsum : (∑ y : ι, ‖∑ z : κ, eC (φ y z)‖ ^ (2 * k)) =
      (∑ u : Fin k → κ, ∑ v : Fin k → κ, K u v).re := by
    calc
      _ = ∑ y : ι, (∑ u : Fin k → κ, ∑ v : Fin k → κ,
          eC (∑ i : Fin k, (φ y (u i) - φ y (v i)))).re := by
        apply Finset.sum_congr rfl
        intro y _
        exact congrArg Complex.re (leafW_even_moment_expansion (φ y) k)
      _ = _ := by
        simp only [K, Complex.re_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
  have hfirst := LeanLab.ExceptionalSet.Decomp538a.first_holder_step
    Finset.univ (fun y : ι => ∑ z : κ, eC (φ y z)) k hk
  rw [Finset.card_univ, hsum] at hfirst
  have hfirst' : ‖∑ y : ι, ∑ z : κ, eC (φ y z)‖ ^ (2 * k) ≤
      (Fintype.card ι : ℝ) ^ (2 * k - 1) *
        ‖∑ u : Fin k → κ, ∑ v : Fin k → κ, K u v‖ :=
    hfirst.trans (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by positivity))
  have hsecond := LeanLab.ExceptionalSet.Decomp538a.first_holder_step
    Finset.univ (fun uv : (Fin k → κ) × (Fin k → κ) => K uv.1 uv.2) k hk
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Fintype.sum_prod_type] at hsecond
  have hcard : ((Fintype.card κ : ℝ) ^ k * (Fintype.card κ : ℝ) ^ k) ^ (2 * k - 1) =
      (Fintype.card κ : ℝ) ^ ((2 * k) * (2 * k - 1)) := by
    rw [← pow_add, ← two_mul, ← pow_mul]
  rw [hcard] at hsecond
  calc
    _ = (‖∑ y : ι, ∑ z : κ, eC (φ y z)‖ ^ (2 * k)) ^ (2 * k) := by rw [pow_mul]
    _ ≤ ((Fintype.card ι : ℝ) ^ (2 * k - 1) *
        ‖∑ u : Fin k → κ, ∑ v : Fin k → κ, K u v‖) ^ (2 * k) :=
      pow_le_pow_left₀ (by positivity) hfirst' _
    _ = (Fintype.card ι : ℝ) ^ ((2 * k - 1) * (2 * k)) *
        ‖∑ u : Fin k → κ, ∑ v : Fin k → κ, K u v‖ ^ (2 * k) := by
      rw [mul_pow, ← pow_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hsecond
        (by positivity : 0 ≤ (Fintype.card ι : ℝ) ^ ((2 * k - 1) * (2 * k)))
      simpa only [K, mul_assoc] using h

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
