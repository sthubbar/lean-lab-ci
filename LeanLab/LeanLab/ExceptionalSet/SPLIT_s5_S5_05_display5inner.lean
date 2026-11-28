import LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_karW_display5

/-!
Split of `leaf_karW_display5_inner` of
`LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_karW_display5`, burst-20261127, CLOUD S5 unit S5-05.
A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971), p. 246, display (5) and the lines before it.

Notation. `J_k(λ)` is the number of solutions of the system
`z_1^j + ... + z_k^j - z_{k+1}^j - ... - z_{2k}^j = λ_j`, `1 ≤ j ≤ n`, `0 ≤ z_i ≤ M`, and
`λ` runs over the box `|λ_j| ≤ k M^j`. In Lean the index `j : Fin n` stands for the power `j + 1`.

Pieces.
* `karJsol`, `karLamBox`: the definitions of `J_k(λ)` and of the box.
* `leaf_karJ_expand`, LEAF MEDIUM: `|Σ_z e(c + Σ_j β_j z^j)|^{2k} = Σ_λ J_k(λ) e(Σ_j β_j λ_j)`.
* `leaf_karJ_sum`, LEAF MEDIUM: `Σ_λ J_k(λ) = (M+1)^{2k}`.
* `leaf_karJ_le_zero`, LEAF MEDIUM: `J_k(λ) ≤ J_k(0)`.
* `leaf_karJ_zero_integral`, LEAF HARD: `J_k(0) = ∫_{[0,1]^n} |Σ_y e(α_1 y + ... + α_n y^n)|^{2k}`.
* `leaf_karJ_second_expansion`, LEAF MEDIUM: `Σ_λ |S(λ)|^{2k} ≤ J_k(0) ∏_s 𝔖_s`.
* `karW_display5_phase`, the rewriting of `Σ_{j=1}^n B_j (yz)^j`, proved.
* `karW_display5_first`, the first expansion and the triangle inequality,
  `Σ_y a_y^{2k} ≤ Σ_λ J_k(λ) |S(λ)|`, proved from `leaf_karJ_expand`.
* `leaf_karW_display5_inner_of_leaves`, the exact statement of `leaf_karW_display5_inner`,
  proved from the pieces with Lemma 4 b, `holder_weighted`.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- `J_k(λ)`, Karacuba p. 246: the number of pairs of `k`-tuples `z, w` with entries in
`[0, M]` and `Σ_i z_i^{j+1} - Σ_i w_i^{j+1} = λ_j` for every `j : Fin n`. -/
def karJsol (n k M : ℕ) (l : Fin n → ℤ) : ℕ :=
  ((Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))).filter
    (fun p => ∀ j : Fin n, (∑ i, ((p.1 i : ℕ) : ℤ) ^ ((j : ℕ) + 1))
      - ∑ i, ((p.2 i : ℕ) : ℤ) ^ ((j : ℕ) + 1) = l j)).card

/-- The box `|λ_j| ≤ k M^j` of Karacuba p. 246, where the sums over `λ` run, with `j : Fin n`
standing for the power `j + 1`. -/
def karLamBox (n k M : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun j : Fin n =>
    Finset.Icc (-((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ)) ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ))

/-- LEAF: the expansion of `a_y^{2k}` through `J_k(λ)`, Karacuba p. 246, first line of the
proof after display (4), class MEDIUM. For real `c` and coefficients `β_j`,
`|Σ_{z ≤ M} e(c + Σ_j β_j z^j)|^{2k} = Σ_{λ} J_k(λ) e(Σ_j β_j λ_j)`: write `|S|^{2k} = S^k conj(S)^k`,
multiply out over pairs of `k`-tuples, `c` cancels, group by the value `λ` of the power sum
differences, which lies in the box since `0 ≤ z^j ≤ M^j`. -/
theorem leaf_karJ_expand (n k M : ℕ) (c : ℝ) (β : Fin n → ℝ) :
    (((‖∑ z ∈ Finset.range (M + 1), eC (c + ∑ j : Fin n, β j * (z : ℝ) ^ ((j : ℕ) + 1))‖
        ^ (2 * k) : ℝ)) : ℂ)
      = ∑ l ∈ karLamBox n k M, (karJsol n k M l : ℂ) * eC (∑ j : Fin n, β j * (l j : ℝ)) := by
  sorry

/-- LEAF: `Σ_λ J_k(λ) = (M+1)^{2k}`, Karacuba p. 246, class MEDIUM: every pair of `k`-tuples is
counted once, at the value `λ` of its power sum differences, which lies in the box. -/
theorem leaf_karJ_sum (n k M : ℕ) :
    ∑ l ∈ karLamBox n k M, (karJsol n k M l : ℝ) = ((M : ℝ) + 1) ^ (2 * k) := by
  sorry

/-- LEAF: `J_k(λ) ≤ J_k(0)`, Karacuba p. 246, class MEDIUM. With `r(u)` the number of
`k`-tuples with power sum vector `u`, `J_k(λ) = Σ_u r(u + λ) r(u) ≤ Σ_u r(u)^2 = J_k(0)` by
Cauchy Schwarz; the paper reads it off the integral formula. -/
theorem leaf_karJ_le_zero (n k M : ℕ) (l : Fin n → ℤ) :
    karJsol n k M l ≤ karJsol n k M 0 := by
  sorry

/-- LEAF: the integral formula for `J_k(0)`, Karacuba p. 246, class HARD:
`J_k(0) = ∫_{[0,1]^n} |Σ_{y ≤ M} e(α_1 y + ... + α_n y^n)|^{2k} dα`, by expanding the
`2k`-th power and the orthogonality `∫_0^1 e(mα) dα = [m = 0]` in each coordinate. -/
theorem leaf_karJ_zero_integral (n k M : ℕ) :
    (karJsol n k M 0 : ℝ)
      = ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k) := by
  sorry

/-- LEAF: the second expansion, Karacuba p. 246, display (5) right side, class MEDIUM. With
`S(λ) = Σ_{y ≤ M} e(Σ_j B_j λ_j y^j)`: by `leaf_karJ_expand` with `c = 0`, `β_j = B_j λ_j`,
`Σ_λ |S(λ)|^{2k} = Σ_μ J_k(μ) ∏_j Σ_{|λ_j| ≤ kM^j} e(B_j λ_j μ_j)`, then `J_k(μ) ≤ J_k(0)` and
the product of sums over the box is a product over `s = 1, ..., n` of
`𝔖_s = Σ_{|μ| ≤ kM^s} |Σ_{|λ| ≤ kM^s} e(B_s λ μ)|`. -/
theorem leaf_karJ_second_expansion (n k M : ℕ) (B : ℕ → ℝ) :
    ∑ l ∈ karLamBox n k M,
        ‖∑ y ∈ Finset.range (M + 1),
          eC (∑ j : Fin n, B ((j : ℕ) + 1) * (l j : ℝ) * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)
      ≤ (karJsol n k M 0 : ℝ) *
        ∏ s ∈ Finset.Icc 1 n, ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖ := by
  sorry

/-- The phase of `a_y`, Karacuba p. 246: `Σ_{j=1}^n B_j (yz)^j = Σ_{j : Fin n} (B_{j+1} y^{j+1}) z^{j+1}`. -/
theorem karW_display5_phase (n : ℕ) (B : ℕ → ℝ) (y z : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j)
      = ∑ j : Fin n, (B ((j : ℕ) + 1) * (y : ℝ) ^ ((j : ℕ) + 1)) * (z : ℝ) ^ ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    congr 1
    push_cast
    ring

/-- The first expansion and the triangle inequality, Karacuba p. 246:
`Σ_y a_y^{2k} ≤ Σ_λ J_k(λ) |Σ_y e(Σ_j B_j λ_j y^j)|`. -/
theorem karW_display5_first (n k M : ℕ) (c : ℝ) (B : ℕ → ℝ) :
    ∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k)
      ≤ ∑ l ∈ karLamBox n k M, (karJsol n k M l : ℝ) *
          ‖∑ y ∈ Finset.range (M + 1),
            eC (∑ j : Fin n, B ((j : ℕ) + 1) * (l j : ℝ) * (y : ℝ) ^ ((j : ℕ) + 1))‖ := by
  have hexp : ∀ y : ℕ, ((‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k) : ℝ) : ℂ)
      = ∑ l ∈ karLamBox n k M, (karJsol n k M l : ℂ) *
          eC (∑ j : Fin n, B ((j : ℕ) + 1) * (l j : ℝ) * (y : ℝ) ^ ((j : ℕ) + 1)) := by
    intro y
    have h := leaf_karJ_expand n k M c (fun j => B ((j : ℕ) + 1) * (y : ℝ) ^ ((j : ℕ) + 1))
    simp only [karW_display5_phase] at h ⊢
    rw [h]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 2
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  set L : ℝ := ∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k) with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hLc : (L : ℂ) = ∑ l ∈ karLamBox n k M, (karJsol n k M l : ℂ) *
      ∑ y ∈ Finset.range (M + 1),
        eC (∑ j : Fin n, B ((j : ℕ) + 1) * (l j : ℝ) * (y : ℝ) ^ ((j : ℕ) + 1)) := by
    rw [hL, Complex.ofReal_sum]
    simp only [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  calc L = ‖(L : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hL0]
    _ ≤ _ := by
      rw [hLc]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [norm_mul, Complex.norm_natCast]

/-- The exact statement of `leaf_karW_display5_inner`, from the pieces. -/
theorem leaf_karW_display5_inner_of_leaves (n k M : ℕ) (hk : 1 ≤ k) (c : ℝ) (B : ℕ → ℝ) :
    (∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k)) ^ (2 * k)
      ≤ ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) *
        (∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)) ^ 2 *
        ∏ s ∈ Finset.Icc 1 n, ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖ := by
  rw [← leaf_karJ_zero_integral n k M]
  set S : (Fin n → ℤ) → ℝ := fun l => ‖∑ y ∈ Finset.range (M + 1),
      eC (∑ j : Fin n, B ((j : ℕ) + 1) * (l j : ℝ) * (y : ℝ) ^ ((j : ℕ) + 1))‖ with hS
  set u : (Fin n → ℤ) → ℝ := fun l => (karJsol n k M l : ℝ) with hu
  set Pr : ℝ := ∏ s ∈ Finset.Icc 1 n, ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖ with hPr
  set J0 : ℝ := (karJsol n k M 0 : ℝ) with hJ0
  have hfirst := karW_display5_first n k M c B
  have hL0 : 0 ≤ ∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k) :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hhold := holder_weighted (karLamBox n k M) (2 * k) (by omega) u S
    (fun l => Nat.cast_nonneg _) (fun l => norm_nonneg _)
  have hsum : ∑ l ∈ karLamBox n k M, u l = ((M : ℝ) + 1) ^ (2 * k) := leaf_karJ_sum n k M
  have hJle : ∑ l ∈ karLamBox n k M, u l * S l ^ (2 * k)
      ≤ J0 * ∑ l ∈ karLamBox n k M, S l ^ (2 * k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun l _ => ?_)
    exact mul_le_mul_of_nonneg_right (by simp only [hu, hJ0]; exact_mod_cast leaf_karJ_le_zero n k M l)
      (pow_nonneg (norm_nonneg _) _)
  have hsec : ∑ l ∈ karLamBox n k M, S l ^ (2 * k) ≤ J0 * Pr := leaf_karJ_second_expansion n k M B
  have hJ00 : 0 ≤ J0 := Nat.cast_nonneg _
  have hpow : (((M : ℝ) + 1) ^ (2 * k)) ^ (2 * k - 1) = ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) := by
    rw [← pow_mul]
    congr 1
    zify [show 1 ≤ 2 * k by omega, show 2 * k ≤ 4 * k ^ 2 by nlinarith]
    ring
  have hMp : 0 ≤ ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) := by positivity
  calc _ ≤ (∑ l ∈ karLamBox n k M, u l * S l) ^ (2 * k) := pow_le_pow_left₀ hL0 hfirst _
    _ ≤ (∑ l ∈ karLamBox n k M, u l) ^ (2 * k - 1) * ∑ l ∈ karLamBox n k M, u l * S l ^ (2 * k) :=
        hhold
    _ = ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) * ∑ l ∈ karLamBox n k M, u l * S l ^ (2 * k) := by
        rw [hsum, hpow]
    _ ≤ ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) * (J0 * (J0 * Pr)) := by
        gcongr
        exact hJle.trans (mul_le_mul_of_nonneg_left hsec hJ00)
    _ = _ := by ring

example : type_of% @leaf_karW_display5_inner := leaf_karW_display5_inner_of_leaves

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
