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
* `leaf_karJ_expand`, proved by CLOUD S5-05c: `|Σ_z e(c + Σ_j β_j z^j)|^{2k} = Σ_λ J_k(λ) e(Σ_j β_j λ_j)`.
* `leaf_karJ_sum`, proved by CLOUD S5-05b: `Σ_λ J_k(λ) = (M+1)^{2k}`.
* `leaf_karJ_le_zero`, proved by CLOUD S5-05b: `J_k(λ) ≤ J_k(0)`.
* `leaf_karJ_zero_integral`, LEAF HARD: `J_k(0) = ∫_{[0,1]^n} |Σ_y e(α_1 y + ... + α_n y^n)|^{2k}`.
* `leaf_karJ_second_expansion`, proved by CLOUD S5-05c: `Σ_λ |S(λ)|^{2k} ≤ J_k(0) ∏_s 𝔖_s`.
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

/-- The expansion of `a_y^{2k}` through `J_k(λ)`, Karacuba p. 246, first line of the
proof after display (4), proved. For real `c` and coefficients `β_j`,
`|Σ_{z ≤ M} e(c + Σ_j β_j z^j)|^{2k} = Σ_{λ} J_k(λ) e(Σ_j β_j λ_j)`: write `|S|^{2k} = S^k conj(S)^k`,
multiply out over pairs of `k`-tuples, `c` cancels, group by the value `λ` of the power sum
differences, which lies in the box since `0 ≤ z^j ≤ M^j`. -/
theorem leaf_karJ_expand (n k M : ℕ) (c : ℝ) (β : Fin n → ℝ) :
    (((‖∑ z ∈ Finset.range (M + 1), eC (c + ∑ j : Fin n, β j * (z : ℝ) ^ ((j : ℕ) + 1))‖
        ^ (2 * k) : ℝ)) : ℂ)
      = ∑ l ∈ karLamBox n k M, (karJsol n k M l : ℂ) * eC (∑ j : Fin n, β j * (l j : ℝ)) := by
  classical
  set φ : ℕ → ℝ := fun z => c + ∑ j : Fin n, β j * (z : ℝ) ^ ((j : ℕ) + 1) with hφ
  set g : (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)) → (Fin n → ℤ) := fun p j =>
    (∑ i, ((p.1 i : ℕ) : ℤ) ^ ((j : ℕ) + 1)) - ∑ i, ((p.2 i : ℕ) : ℤ) ^ ((j : ℕ) + 1) with hg
  set F : (Fin n → ℤ) → ℂ := fun l => eC (∑ j : Fin n, β j * (l j : ℝ)) with hF
  set S : ℂ := ∑ z ∈ Finset.range (M + 1), eC (φ z) with hS
  have hconj : ∀ x : ℝ, (starRingEnd ℂ) (eC x) = eC (-x) := by
    intro x
    unfold eC
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    push_cast
    ring
  have hsum : ∀ (s : Finset (Fin k)) (f : Fin k → ℝ), eC (∑ i ∈ s, f i) = ∏ i ∈ s, eC (f i) := by
    intro s f
    unfold eC
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  have hnorm : (((‖S‖ ^ (2 * k) : ℝ)) : ℂ) = S ^ k * (starRingEnd ℂ S) ^ k := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    rfl
  have hSfin : S = ∑ a : Fin (M + 1), eC (φ a) := by rw [hS, Finset.sum_range]
  have hSk : S ^ k = ∑ z : Fin k → Fin (M + 1), eC (∑ i, φ (z i)) := by
    rw [hSfin, ← Fin.prod_const, Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hsum]
  have hSk' : (starRingEnd ℂ S) ^ k = ∑ w : Fin k → Fin (M + 1), eC (-∑ i, φ (w i)) := by
    rw [← map_pow, hSk, map_sum]
    simp only [hconj]
  have hterm : ∀ p : (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)),
      eC (∑ i, φ (p.1 i)) * eC (-∑ i, φ (p.2 i)) = F (g p) := by
    intro p
    rw [← karW_eC_add, hF]
    congr 1
    simp only [hφ, hg, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have e1 : ∀ q : Fin k → Fin (M + 1), ∑ i, ∑ j : Fin n, β j * ((q i : ℕ) : ℝ) ^ ((j : ℕ) + 1)
        = ∑ j : Fin n, β j * ∑ i, ((q i : ℕ) : ℝ) ^ ((j : ℕ) + 1) := fun q => by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    rw [e1, e1]
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hmaps : ∀ p ∈ (Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))),
      g p ∈ karLamBox n k M := by
    intro p _
    simp only [karLamBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have hb : ∀ q : Fin k → Fin (M + 1), 0 ≤ ∑ i, ((q i : ℕ) : ℤ) ^ ((j : ℕ) + 1) ∧
        ∑ i, ((q i : ℕ) : ℤ) ^ ((j : ℕ) + 1) ≤ ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by
      intro q
      refine ⟨Finset.sum_nonneg (fun i _ => by positivity), ?_⟩
      calc ∑ i, ((q i : ℕ) : ℤ) ^ ((j : ℕ) + 1) ≤ ∑ _i : Fin k, ((M : ℤ)) ^ ((j : ℕ) + 1) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have : ((q i : ℕ) : ℤ) ≤ M := by have := (q i).isLt; omega
            exact pow_le_pow_left₀ (by positivity) this _
        _ = ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by simp
    have h1 := hb p.1
    have h2 := hb p.2
    simp only [hg]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hJ : ∀ l, karJsol n k M l = ((Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))).filter
      (fun p => g p = l)).card := by
    intro l
    unfold karJsol
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg, funext_iff]
  rw [hnorm, hSk, hSk', Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  simp only [hterm]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => F l) (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
    Finset.sum_const, nsmul_eq_mul, hJ l]

/-- `Σ_λ J_k(λ) = (M+1)^{2k}`, Karacuba p. 246, proved: every pair of `k`-tuples is
counted once, at the value `λ` of its power sum differences, which lies in the box. -/
theorem leaf_karJ_sum (n k M : ℕ) :
    ∑ l ∈ karLamBox n k M, (karJsol n k M l : ℝ) = ((M : ℝ) + 1) ^ (2 * k) := by
  classical
  set g : (Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)) → (Fin n → ℤ) := fun p j =>
    (∑ i, ((p.1 i : ℕ) : ℤ) ^ ((j : ℕ) + 1)) - ∑ i, ((p.2 i : ℕ) : ℤ) ^ ((j : ℕ) + 1) with hg
  have hmaps : ∀ p ∈ (Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))),
      g p ∈ karLamBox n k M := by
    intro p _
    simp only [karLamBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have hb : ∀ q : Fin k → Fin (M + 1), 0 ≤ ∑ i, ((q i : ℕ) : ℤ) ^ ((j : ℕ) + 1) ∧
        ∑ i, ((q i : ℕ) : ℤ) ^ ((j : ℕ) + 1) ≤ ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by
      intro q
      refine ⟨Finset.sum_nonneg (fun i _ => by positivity), ?_⟩
      calc ∑ i, ((q i : ℕ) : ℤ) ^ ((j : ℕ) + 1) ≤ ∑ _i : Fin k, ((M : ℤ)) ^ ((j : ℕ) + 1) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have : ((q i : ℕ) : ℤ) ≤ M := by have := (q i).isLt; omega
            exact pow_le_pow_left₀ (by positivity) this _
        _ = ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by simp
    have h1 := hb p.1
    have h2 := hb p.2
    simp only [hg]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hJ : ∀ l, karJsol n k M l = ((Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))).filter
      (fun p => g p = l)).card := by
    intro l
    unfold karJsol
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg, funext_iff]
  simp only [hJ]
  rw [← Nat.cast_sum, ← hcard]
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

/-- `J_k(λ) ≤ J_k(0)`, Karacuba p. 246, proved. With `r(u)` the number of
`k`-tuples with power sum vector `u`, `J_k(λ) = Σ_u r(u + λ) r(u) ≤ Σ_u r(u)^2 = J_k(0)` by
`2ab ≤ a² + b²` termwise; the paper reads it off the integral formula. -/
theorem leaf_karJ_le_zero (n k M : ℕ) (l : Fin n → ℤ) :
    karJsol n k M l ≤ karJsol n k M 0 := by
  classical
  set v : (Fin k → Fin (M + 1)) → (Fin n → ℤ) := fun q j =>
    ∑ i, ((q i : ℕ) : ℤ) ^ ((j : ℕ) + 1) with hv
  set V : Finset (Fin n → ℤ) := Finset.univ.image v with hV
  set r : (Fin n → ℤ) → ℕ := fun u => (Finset.univ.filter (fun q => v q = u)).card with hr
  have hJ : ∀ m : Fin n → ℤ, karJsol n k M m = ∑ u ∈ V, r u * r (u - m) := by
    intro m
    have e1 : karJsol n k M m = ((Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))).filter
        (fun p => v p.2 = v p.1 - m)).card := by
      unfold karJsol
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, funext_iff, Pi.sub_apply]
      constructor
      · intro h j; have := h j; linarith
      · intro h j; have := h j; linarith
    rw [e1, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    have hin : ∀ a : Fin k → Fin (M + 1),
        (∑ b : Fin k → Fin (M + 1), if v b = v a - m then 1 else 0) = r (v a - m) := by
      intro a
      rw [hr]
      simp only [Finset.card_filter]
    simp only [hin]
    rw [Finset.sum_comp (f := fun u => r (u - m)) (g := v)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [smul_eq_mul]
  rw [hJ l, hJ 0]
  simp only [sub_zero]
  have hAM : ∀ u ∈ V, 2 * (r u * r (u - l)) ≤ r u * r u + r (u - l) * r (u - l) := by
    intro u _
    nlinarith [sq_nonneg ((r u : ℤ) - r (u - l))]
  have hshift : ∑ u ∈ V, r (u - l) * r (u - l) ≤ ∑ u ∈ V, r u * r u := by
    have hinj : Set.InjOn (fun u : Fin n → ℤ => u - l) V := fun a _ b _ h => by simpa using h
    rw [← Finset.sum_image (f := fun w => r w * r w) (g := fun u => u - l) hinj]
    refine Finset.sum_le_sum_of_ne_zero (fun w _ hw => ?_)
    have hr0 : r w ≠ 0 := fun h => hw (by simp [h])
    rw [hr] at hr0
    obtain ⟨q, hq⟩ := Finset.card_ne_zero.mp hr0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [hV]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩
  have h2 : 2 * ∑ u ∈ V, r u * r (u - l) ≤ ∑ u ∈ V, r u * r u + ∑ u ∈ V, r (u - l) * r (u - l) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hAM
  omega

/-- LEAF: the integral formula for `J_k(0)`, Karacuba p. 246, class HARD:
`J_k(0) = ∫_{[0,1]^n} |Σ_{y ≤ M} e(α_1 y + ... + α_n y^n)|^{2k} dα`, by expanding the
`2k`-th power and the orthogonality `∫_0^1 e(mα) dα = [m = 0]` in each coordinate. -/
theorem leaf_karJ_zero_integral (n k M : ℕ) :
    (karJsol n k M 0 : ℝ)
      = ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k) := by
  sorry

/-- `∏_{j : Fin n} G(j+1) = ∏_{s=1}^n G(s)`. -/
theorem karW_prod_fin_shift (n : ℕ) (G : ℕ → ℝ) :
    ∏ j : Fin n, G ((j : ℕ) + 1) = ∏ s ∈ Finset.Icc 1 n, G s := by
  rw [Fin.prod_univ_eq_prod_range (fun j => G (j + 1)) n]
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]

/-- The second expansion, Karacuba p. 246, display (5) right side, proved. With
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
  classical
  set T : Fin n → Finset ℤ := fun j =>
    Finset.Icc (-((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ)) ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ) with hT
  have hbox : karLamBox n k M = Fintype.piFinset T := rfl
  have hexp : ∀ l : Fin n → ℤ, ((‖∑ y ∈ Finset.range (M + 1),
          eC (∑ j : Fin n, B ((j : ℕ) + 1) * (l j : ℝ) * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k) : ℝ) : ℂ)
      = ∑ μ ∈ karLamBox n k M, (karJsol n k M μ : ℂ) *
          ∏ j : Fin n, eC (B ((j : ℕ) + 1) * (l j : ℝ) * (μ j : ℝ)) := by
    intro l
    have h := leaf_karJ_expand n k M 0 (fun j => B ((j : ℕ) + 1) * (l j : ℝ))
    simp only [zero_add] at h
    rw [h]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    congr 1
    rw [← karW_eC_sum]
  set h : Fin n → ℤ → ℝ := fun j m => ‖∑ t ∈ T j, eC (B ((j : ℕ) + 1) * (t : ℝ) * (m : ℝ))‖ with hh
  set L : ℝ := ∑ l ∈ karLamBox n k M,
        ‖∑ y ∈ Finset.range (M + 1),
          eC (∑ j : Fin n, B ((j : ℕ) + 1) * (l j : ℝ) * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k) with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hLc : (L : ℂ) = ∑ μ ∈ karLamBox n k M, (karJsol n k M μ : ℂ) *
      ∏ j : Fin n, ∑ t ∈ T j, eC (B ((j : ℕ) + 1) * (t : ℝ) * (μ j : ℝ)) := by
    rw [hL, Complex.ofReal_sum]
    simp only [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [← Finset.mul_sum, Finset.prod_univ_sum, ← hbox]
  have hstep : L ≤ ∑ μ ∈ karLamBox n k M, (karJsol n k M 0 : ℝ) * ∏ j : Fin n, h j (μ j) := by
    calc L = ‖(L : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hL0]
      _ ≤ ∑ μ ∈ karLamBox n k M, ‖(karJsol n k M μ : ℂ) *
            ∏ j : Fin n, ∑ t ∈ T j, eC (B ((j : ℕ) + 1) * (t : ℝ) * (μ j : ℝ))‖ := by
          rw [hLc]; exact norm_sum_le _ _
      _ ≤ _ := by
          refine Finset.sum_le_sum (fun μ _ => ?_)
          rw [norm_mul, Complex.norm_natCast, norm_prod]
          refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
          exact_mod_cast leaf_karJ_le_zero n k M μ
  refine hstep.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, hbox, ← Finset.prod_univ_sum]
  congr 1
  exact karW_prod_fin_shift n (fun s => ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖)

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
