/-
Split of the OPEN target `upper_self_scaled_nonprincipal_distribution` of
SPLIT_upper_self_scaled_conditions into four leaves, one per term of the four term identity for
the self scaled upper coefficient, and an assembly that has the target's statement verbatim and
uses no sorry.

The target asks condition iii of page 3 for the non-principal characters: the short interval sums
of the self scaled upper coefficient, truncated at `t`, save every power of the logarithm
uniformly in the modulus up to `log x ^ A`, in the character other than the trivial one and in
`t`. The coefficient on the window is the recentring factor `log m / log Y` times the raw page 53
weight at level `m`, and the raw weight is the alternating sum of the four terms of the identity
`psi(m, Y^c4) = g_m - h_m + j_m - (kept part of k_m)` with the level measured at `m` itself.

Leaf 1 is the `g` term, leaf 2 the `h` term, leaf 3 the `j` term and leaf 4 the kept part of the
`k` term, each with the same `A`, `x`, `q`, `chi`, `t` quantifiers as the target and with the whole
recentring factor inside the summand, so each is one summand of the target's sum and strictly
weaker than it. The assembly `upper_self_scaled_nonprincipal_distribution_split` splits the
summand by the identity, sums the four pieces with subadditivity of the norm, and takes one
constant serving the four pieces and the threshold at once.

The four leaves remain OPEN. This file adds no definition, changes no existing file, and leaves the
sealed statement untouched. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_conditions

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-! ### Elementary complex bookkeeping used by the assembly -/

/-- A sum of four alternating complex pieces is the alternating sum of the four sums. -/
private lemma sum_four_sub (s : Finset ℕ) (f g h k : ℕ → ℂ) :
    (∑ m ∈ s, (f m - g m + h m - k m)) =
      (∑ m ∈ s, f m) - (∑ m ∈ s, g m) + (∑ m ∈ s, h m) - (∑ m ∈ s, k m) := by
  have h1 : ∀ m, (f m - g m + h m - k m) = (f m - g m) + (h m - k m) := by
    intro m
    abel
  simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

/-- A real factor in front of an alternating sum of four real pieces multiplies each piece. -/
private lemma ofReal_mul_four (a b c d e : ℝ) (z : ℂ) :
    ((a * (b - c + d - e) : ℝ) : ℂ) * z =
      ((a * b : ℝ) : ℂ) * z - ((a * c : ℝ) : ℂ) * z + ((a * d : ℝ) : ℂ) * z -
        ((a * e : ℝ) : ℂ) * z := by
  push_cast
  ring

/-- The norm of an alternating sum of four complex numbers is at most the sum of the four norms. -/
private lemma norm_sub_add_sub_le (a b c d : ℂ) :
    ‖a - b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 : a - b + c - d = (a - b) + (c - d) := by abel
  rw [h1]
  calc ‖(a - b) + (c - d)‖ ≤ ‖a - b‖ + ‖c - d‖ := norm_add_le _ _
    _ ≤ (‖a‖ + ‖b‖) + (‖c‖ + ‖d‖) := add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring

/-! ### The four terms of the identity, one at a time -/

/-- LEAF: the `g` term of the identity. The first term of the page 53 raw weight, the sifted
indicator at the level `m ^ c4`, taken with the recentring factor `log m / log Y`, against a
non-principal character over the truncated right interval, is bounded by
`C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`. This is one summand of the
target's sum, so it is strictly easier than the target; it is the term the prime numbers fall into,
and it is the place where the sifted count has to be distributed over the residue classes.
Non-vacuity: at `t = 0` the index set is empty and the sum is zero. -/
theorem leaf_g_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperG ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the `h` term of the identity. The second term of the page 53 raw weight, the sum over one
prime factor at a level between `m ^ c1` and `m ^ c4` of the sifted indicator of the cofactor,
again with the recentring factor and against a non-principal character over the truncated right
interval, is bounded by `C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`.
One summand of the target's sum and strictly easier than the target. Non-vacuity: at `t = 0` the
index set is empty and the sum is zero. -/
theorem leaf_h_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperH ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the `j` term of the identity. The third term of the page 53 raw weight, the sum over two
decreasing prime factors at levels between `m ^ c1` and `m ^ c4` of the sifted indicator of the
cofactor, with the recentring factor and against a non-principal character over the truncated right
interval, is bounded by `C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`. One
summand of the target's sum and strictly easier than the target. Non-vacuity: at `t = 0` the index
set is empty and the sum is zero. -/
theorem leaf_j_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperJ ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the kept part of the `k` term of the identity. The fourth term of the page 53 raw weight,
the part of the three prime sum on which the covering lemma applies to an arrangement of the three
exponents, with the recentring factor and against a non-principal character over the truncated
right interval, is bounded by `C x^(11/20+eps) (log x)^(-A)` with a constant depending only on `A`.
One summand of the target's sum and strictly easier than the target: it is at most the `k` term
itself, since the deleted terms are removed rather than added. Non-vacuity: at `t = 0` the index
set is empty and the sum is zero. -/
theorem leaf_kept_term_nonprincipal
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-! ### Assembly -/

/-- The target `upper_self_scaled_nonprincipal_distribution` of
SPLIT_upper_self_scaled_conditions, verbatim, assembled from the four leaves. For each power of the
logarithm the four leaves give four constants; the largest of them raised to at least four serves
as the single constant of the statement, both as the threshold beyond which `x` is passed to the
leaves and as the multiplier of `x^(11/20+eps) (log x)^(-A)`. On the index set the coefficient is
the recentring factor times `g - h + j - kept`, by the four term identity at the level `m`, so the
sum splits into the four sums of the leaves and subadditivity of the norm gives the bound. No step
uses the sealed target. -/
theorem upper_self_scaled_nonprincipal_distribution_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b1 x m : ℂ) * χ (m : ZMod q))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨Cg, hCg⟩ := leaf_g_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  obtain ⟨Ch, hCh⟩ := leaf_h_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  obtain ⟨Cj, hCj⟩ := leaf_j_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  obtain ⟨Ck, hCk⟩ := leaf_kept_term_nonprincipal h4 h9 hω hz hε hε8 A hA
  refine ⟨max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4,
    fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hCgK : Cg ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hChK : Ch ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hCjK : Cj ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hCkK : Ck ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hK1 : (1 : ℝ) ≤ max (max Cg Ch) (max (max Cj Ck) 1) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKM : max (max Cg Ch) (max (max Cj Ck) 1) ≤
      max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4 := by
    have h0 : (0 : ℝ) ≤ max (max Cg Ch) (max (max Cj Ck) 1) := le_trans (by norm_num) hK1
    have h4' : max (max Cg Ch) (max (max Cj Ck) 1) ≤
        4 * max (max Cg Ch) (max (max Cj Ck) 1) := by nlinarith
    exact le_trans h4' (le_max_left _ _)
  have hxg : Cg ≤ x := le_trans (le_trans hCgK hKM) hx
  have hxh : Ch ≤ x := le_trans (le_trans hChK hKM) hx
  have hxj : Cj ≤ x := le_trans (le_trans hCjK hKM) hx
  have hxk : Ck ≤ x := le_trans (le_trans hCkK hKM) hx
  have hY0 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hL0 : (0 : ℝ) ≤ Real.log x ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hYL : (0 : ℝ) ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := mul_nonneg hY0 hL0
  have hY2 : (2 : ℝ) ≤ x ^ (11 / 20 + ε) := upper_Y_ge_two hε hx4
  have hpt : ∀ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      ((b1 x m : ℂ) * χ (m : ZMod q)) =
        ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) -
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) +
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) -
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperKept ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q) := by
    intro m hm
    have hmI : m ∈ rightInterval ε x := (Finset.mem_filter.mp hm).1
    have hmY : (⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) < m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hmY
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hmpos
    have hraw4 : upperRawWeight ε (m : ℝ) m =
        upperG ε (m : ℝ) m - upperH ε (m : ℝ) m + upperJ ε (m : ℝ) m -
          upperKept ε (m : ℝ) m := by
      rw [upper_raw_eq_rough_add_deleted ε (Y := (m : ℝ)) hm1 m,
        upper_rough_four_term ε (Y := (m : ℝ)) hm1 m]
      unfold upperDeletedSum
      ring
    rw [hb x m, if_pos ⟨hY2, hmI⟩, hraw4]
    exact ofReal_mul_four _ _ _ _ _ _
  have hsum : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((b1 x m : ℂ) * χ (m : ZMod q)) =
      (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) +
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
            upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)) := by
    rw [show ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) * χ (m : ZMod q)) =
        ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q) -
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q) +
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q) -
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q))
      from Finset.sum_congr rfl hpt]
    exact sum_four_sub _ _ _ _ _
  have hG := hCg x hxg q hq hqA χ hχ t ht
  have hH := hCh x hxh q hq hqA χ hχ t ht
  have hJ := hCj x hxj q hq hqA χ hχ t ht
  have hK := hCk x hxk q hq hqA χ hχ t ht
  rw [hsum]
  calc ‖(∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) +
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
            χ (m : ZMod q)) -
        (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
            upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q))‖
      ≤ ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperG ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q)‖ +
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperH ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q)‖ +
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperJ ε (m : ℝ) m : ℝ) : ℂ) *
              χ (m : ZMod q)‖ +
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperKept ε (m : ℝ) m : ℝ) : ℂ) * χ (m : ZMod q)‖ :=
        norm_sub_add_sub_le _ _ _ _
    _ ≤ Cg * x ^ (11 / 20 + ε) * Real.log x ^ (-A) + Ch * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        Cj * x ^ (11 / 20 + ε) * Real.log x ^ (-A) + Ck * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
          linarith [hG, hH, hJ, hK]
    _ = (Cg + Ch + Cj + Ck) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    _ ≤ (4 * max (max Cg Ch) (max (max Cj Ck) 1)) *
          (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
          apply mul_le_mul_of_nonneg_right _ hYL
          nlinarith [hCgK, hChK, hCjK, hCkK]
    _ ≤ max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4 *
          (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hYL
    _ = max (4 * max (max Cg Ch) (max (max Cj Ck) 1)) 4 * x ^ (11 / 20 + ε) *
          Real.log x ^ (-A) := by ring

end LeanLab.BHP1997.Upper312Route
