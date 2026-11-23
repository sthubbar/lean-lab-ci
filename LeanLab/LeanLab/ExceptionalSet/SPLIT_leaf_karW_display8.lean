/-
Split of `leaf_karW_display8` of `LeanLab.ExceptionalSet.SPLIT_leaf_karW_taylor_sum_bound`,
display (8) of A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971), p. 247, along its proof,
p. 245 last line to p. 247. All displays were read from the page images, rendered at 200 dpi.

Pieces, one per display. All pieces are PROVED; the assembly is PROVED CONDITIONAL ON
KarLemma1, Lemma 1 of p. 243, a hypothesis of the target. No open leaves remain here.
* `karCapRecip`, `karSigma`, `karJ0`, `karPowVec`, `karSy`, `karBox`: the capped reciprocal
  `min(U, 1/(γ))` of display (6), the sums `𝔖_s`, `J_k(0)` as a count, the power sums, the
  sum `Σ_y e(B_1 λ_1 y + ... + B_n λ_n y^n)` and the box `|λ_s| ≤ k P2^s`, all of p. 246.
* `karW_display6_geom`, `karW_sym_geom`: `|Σ_{m=1}^U e(αm)| ≤ min(U, 1/(α))`, p. 246 before
  (6), and its symmetric form.
* `karW_display5_holder`: display (5), Lemma 4 a and b, the two Holder steps.
* `karPowVec_sub_mem_box`, `karW_property_ac`: properties c and a of `J_k(λ)`.
* `karW_display6_expand`, `karW_display6_box`, `karW_display5_6`: display (6),
  `|W_1(a)|^{4k²} ≤ (P2+1)^{8k²-4k} J_k(0)² Π_s 𝔖_s`.
* `karJ0_le_shifted`, `karJ0_lemma1`: Lemma 1 for `J_k(0)` with `b = k = b_l`, through the
  translation `y → y + 1`. CONDITIONAL ON KarLemma1.
* `karSigma_trivial`, `karW_display7_factor`, `karW_display7`, with `karW_factor_sum_le`,
  `karW_n0_cube`, `karW_sigma_product`: display (7) and the estimate of `𝔖` after it, from
  the proved Lemma 3 forms of `Decomp538a`; the slips `2^s`, `4^s` of the paper and the
  change `P2 → P2 + 1` are absorbed into `4^{n(n+1)}`.
* `karW_pow_m`, `karW_D_sq`, `karW_m_pow_x`, `karW_combine`, `karW_root`: the combination
  and the `4k²`-th root of p. 247; the slip `2^{8k²}` missing from `B` becomes `C0 = 8`.
* `leaf_karW_display8_split`: the assembly, exactly the type of `leaf_karW_display8`.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_karW_taylor_sum_bound

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Definitions of p. 246 -/

/-- The capped reciprocal `min(U, 1/(γ))` of Karacuba p. 246, display (6), with value `U`
where `(γ) = 0`: there the geometric sum has `U` terms equal to `1`, and Lean's `1/0 = 0`
would make display (6) false, see `Decomp538a.geometric_bound_needs_zero_convention`. -/
noncomputable def karCapRecip (U γ : ℝ) : ℝ :=
  if Int.fract γ = 0 then U else min U (1 / nint γ)

/-- The sum `𝔖_s = Σ_{|μ| ≤ k P2^s} min(2k P2^s + 1, 1/(B_s μ))` of Karacuba p. 246, after
display (6), with `M = P2` and `β = B_s`. -/
noncomputable def karSigma (k M s : ℕ) (β : ℝ) : ℝ :=
  ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
    karCapRecip ((2 * (k * M ^ s) + 1 : ℕ) : ℝ) (β * μ)

/-- `J_k(0, ..., 0)` of Karacuba p. 246: the number of pairs of `k`-tuples `u, v` from
`0, ..., M` with `Σ u_i^j = Σ v_i^j` for `j = 1, ..., n`; it equals the integral of
`|Σ_{y=0}^{M} e(α_1 y + ... + α_n y^n)|^{2k}` over the unit cube. -/
noncomputable def karJ0 (n k M : ℕ) : ℝ :=
  ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
    if (∀ j : Fin n, ∑ i : Fin k, ((u i : ℕ) : ℝ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin k, ((v i : ℕ) : ℝ) ^ ((j : ℕ) + 1)) then (1 : ℝ) else 0

theorem karCapRecip_nonneg {U : ℝ} (hU : 0 ≤ U) (γ : ℝ) : 0 ≤ karCapRecip U γ := by
  unfold karCapRecip nint
  split_ifs
  · exact hU
  · refine le_min hU ?_
    have h1 := Int.fract_nonneg γ
    have h2 := Int.fract_lt_one γ
    have : 0 ≤ min (Int.fract γ) (1 - Int.fract γ) := le_min h1 (by linarith)
    positivity

theorem karSigma_nonneg (k M s : ℕ) (β : ℝ) : 0 ≤ karSigma k M s β :=
  Finset.sum_nonneg fun _ _ => karCapRecip_nonneg (by positivity) _

theorem karJ0_nonneg (n k M : ℕ) : 0 ≤ karJ0 n k M := by
  unfold karJ0
  refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
  split_ifs <;> norm_num

/-! ### The geometric sum, p. 246 -/

/-- PROVED. Karacuba p. 246, the line before display (6): for an integer `U ≥ 1`,
`|Σ_{m=1}^U e(αm)| ≤ min(U, 1/(α))`, with the value `U` where `(α) = 0`; it holds for `U = 0`
too. From the proved `Decomp538a.geometric_sum_bound`. -/
theorem karW_display6_geom (U : ℕ) (α : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 U, eC (α * m)‖ ≤ karCapRecip U α := by
  unfold karCapRecip nint
  exact LeanLab.ExceptionalSet.Decomp538a.geometric_sum_bound U α

/-! ### Displays (5) and (6) -/

/-- The power sums `Σ_i u_i^{j+1}`, `j = 0, ..., n-1`, of a `k`-tuple from `0, ..., M`: the
left sides of the system that defines `J_k(λ)`, Karacuba p. 246. -/
def karPowVec (n k M : ℕ) (u : Fin k → Fin (M + 1)) : Fin n → ℤ :=
  fun j => ∑ i : Fin k, ((u i : ℕ) : ℤ) ^ ((j : ℕ) + 1)

/-- The sum `Σ_{y=0}^{P2} e(B_1 λ_1 y + ... + B_n λ_n y^n)` of Karacuba p. 246, with
`lam j = λ_{j+1}`, `β s = B_s`, `M = P2`. -/
noncomputable def karSy (n M : ℕ) (β : ℕ → ℝ) (lam : Fin n → ℤ) : ℂ :=
  ∑ y : Fin (M + 1),
    eC (∑ j : Fin n, β ((j : ℕ) + 1) * (lam j : ℝ) * ((y : ℕ) : ℝ) ^ ((j : ℕ) + 1))

/-- The box `|λ_s| ≤ k P2^s`, `s = 1, ..., n`, of property c of `J_k(λ)`, Karacuba p. 246. -/
def karBox (n k M : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j : Fin n =>
    Finset.Icc (-((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ)) ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ)

/-- Reindexing `s = 1, ..., n` as `j + 1`, `j : Fin n`. -/
theorem karW_sum_Icc_fin {R : Type*} [AddCommMonoid R] (n : ℕ) (g : ℕ → R) :
    ∑ s ∈ Finset.Icc 1 n, g s = ∑ j : Fin n, g ((j : ℕ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => g (j + 1))]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- Reindexing a product over `s = 1, ..., n` as `j + 1`, `j : Fin n`. -/
theorem karW_prod_Icc_fin {R : Type*} [CommMonoid R] (n : ℕ) (g : ℕ → R) :
    ∏ s ∈ Finset.Icc 1 n, g s = ∏ j : Fin n, g ((j : ℕ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => g (j + 1))]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

/-- PROVED. Display (5) of Karacuba p. 245 last line to p. 246, the two Holder steps,
Lemma 4 a then Lemma 4 b, from the proved `leafW_two_holder_bound`:
`|W_1(a)|^{4k²} ≤ (P2+1)^{8k²-4k} Σ_{u,v} |Σ_y e(B_1 λ_1 y + ... + B_n λ_n y^n)|^{2k}` with
`λ = λ(u, v)` the vector of power sum differences, that is
`Σ_λ J_k(λ) |Σ_y ...|^{2k}` with `J_k(λ)` as a count. -/
theorem karW_display5_holder (n M k : ℕ) (hk : 1 ≤ k) (b : ℝ) (β : ℕ → ℝ) :
    ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      eC (b + ∑ j ∈ Finset.Icc 1 n, β j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (4 * k ^ 2)
      ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) *
        ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
          ‖karSy n M β (karPowVec n k M u - karPowVec n k M v)‖ ^ (2 * k) := by
  have hrange : ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      eC (b + ∑ j ∈ Finset.Icc 1 n, β j * (((y * z : ℕ) : ℝ) ^ j)) =
      ∑ y : Fin (M + 1), ∑ z : Fin (M + 1),
        eC (b + ∑ j ∈ Finset.Icc 1 n, β j * ((((y : ℕ) * (z : ℕ) : ℕ) : ℝ) ^ j)) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_range]
  rw [hrange]
  have h := leafW_two_holder_bound (ι := Fin (M + 1)) (κ := Fin (M + 1))
    (fun y z => b + ∑ j ∈ Finset.Icc 1 n, β j * ((((y : ℕ) * (z : ℕ) : ℕ) : ℝ) ^ j)) k (by omega)
  simp only [Fintype.card_fin] at h
  have hexp : (2 * k) * (2 * k) = 4 * k ^ 2 := by ring
  rw [hexp] at h
  refine h.trans (le_of_eq ?_)
  have hpow : ((M + 1 : ℕ) : ℝ) ^ ((2 * k - 1) * (2 * k)) * ((M + 1 : ℕ) : ℝ) ^ ((2 * k) * (2 * k - 1))
      = ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) := by
    rw [← pow_add]
    push_cast
    congr 1
    zify [show 1 ≤ 2 * k by omega, show 4 * k ≤ 8 * k ^ 2 by nlinarith]
    ring
  rw [hpow]
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  congr 2
  unfold karSy
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  simp only [karPowVec, Pi.sub_apply, add_sub_add_left_eq_sub, karW_sum_Icc_fin]
  push_cast
  simp only [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- PROVED. Property c of `J_k(λ)`, Karacuba p. 246: `|λ_s| ≤ k P2^s` for every difference of
power sums of two `k`-tuples from `0, ..., P2`. -/
theorem karPowVec_sub_mem_box (n k M : ℕ) (u v : Fin k → Fin (M + 1)) :
    karPowVec n k M u - karPowVec n k M v ∈ karBox n k M := by
  rw [karBox, Fintype.mem_piFinset]
  intro j
  have hb : ∀ w : Fin k → Fin (M + 1), 0 ≤ karPowVec n k M w j ∧
      karPowVec n k M w j ≤ ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by
    intro w
    refine ⟨Finset.sum_nonneg fun i _ => by positivity, ?_⟩
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        ((w i : ℕ) : ℤ) ^ ((j : ℕ) + 1) ≤ (M : ℤ) ^ ((j : ℕ) + 1) := by
      intro i _
      have : ((w i : ℕ) : ℤ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (w i).isLt
      exact pow_le_pow_left₀ (by positivity) this _
    have h := Finset.sum_le_card_nsmul _ _ _ hle
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    unfold karPowVec
    push_cast
    exact h
  obtain ⟨hu0, hu1⟩ := hb u
  obtain ⟨hv0, hv1⟩ := hb v
  rw [Finset.mem_Icc, Pi.sub_apply]
  constructor <;> linarith

/-- PROVED. Properties a and c of `J_k(λ)`, Karacuba p. 246: grouping the pairs `(u, v)` by
`λ = λ(u, v)`, every `λ(u, v)` lies in the box `|λ_s| ≤ k P2^s`, property c,
`karPowVec_sub_mem_box`, and `J_k(λ) ≤ J_k(0)`, property a, the proved
`leafW_difference_count_le_zero`; so for every `F ≥ 0`,
`Σ_{u,v} F(λ(u, v)) = Σ_λ J_k(λ) F(λ) ≤ J_k(0) Σ_{λ in the box} F(λ)`. -/
theorem karW_property_ac (n k M : ℕ) (F : (Fin n → ℤ) → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        F (karPowVec n k M u - karPowVec n k M v)
      ≤ karJ0 n k M * ∑ lam ∈ karBox n k M, F lam := by
  classical
  set A := karPowVec n k M with hA
  set cnt : (Fin n → ℤ) → ℝ := fun t =>
    ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1), if A u - A v = t then (1 : ℝ) else 0
    with hcnt
  have hpt : ∀ u v, F (A u - A v) =
      ∑ lam ∈ karBox n k M, (if A u - A v = lam then (1 : ℝ) else 0) * F lam := by
    intro u v
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (karPowVec_sub_mem_box n k M u v)]
  have hfib : ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1), F (A u - A v) =
      ∑ lam ∈ karBox n k M, cnt lam * F lam := by
    calc ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1), F (A u - A v)
        = ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1), ∑ lam ∈ karBox n k M,
            (if A u - A v = lam then (1 : ℝ) else 0) * F lam :=
          Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hpt u v
      _ = ∑ u : Fin k → Fin (M + 1), ∑ lam ∈ karBox n k M, ∑ v : Fin k → Fin (M + 1),
            (if A u - A v = lam then (1 : ℝ) else 0) * F lam :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ lam ∈ karBox n k M, ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
            (if A u - A v = lam then (1 : ℝ) else 0) * F lam := Finset.sum_comm
      _ = ∑ lam ∈ karBox n k M, cnt lam * F lam := by
          refine Finset.sum_congr rfl fun lam _ => ?_
          simp only [hcnt, Finset.sum_mul]
  have hle : ∀ t, cnt t ≤ cnt 0 := fun t => leafW_difference_count_le_zero A t
  have h0 : cnt 0 = karJ0 n k M := by
    rw [hcnt, karJ0]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hiff : (A u - A v = 0) ↔ (∀ j : Fin n, ∑ i : Fin k, ((u i : ℕ) : ℝ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin k, ((v i : ℕ) : ℝ) ^ ((j : ℕ) + 1)) := by
      rw [sub_eq_zero, funext_iff]
      refine forall_congr' fun j => ?_
      rw [hA, karPowVec, karPowVec]
      constructor
      · intro h
        have := congrArg (fun z : ℤ => (z : ℝ)) h
        push_cast at this
        exact this
      · intro h
        have : ((∑ i : Fin k, ((u i : ℕ) : ℤ) ^ ((j : ℕ) + 1) : ℤ) : ℝ) =
            ((∑ i : Fin k, ((v i : ℕ) : ℤ) ^ ((j : ℕ) + 1) : ℤ) : ℝ) := by
          push_cast; exact h
        exact_mod_cast this
    simp only [hiff]
  rw [hfib, ← h0, Finset.mul_sum]
  exact Finset.sum_le_sum fun lam _ => mul_le_mul_of_nonneg_right (hle lam) (hF lam)

theorem karW_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem karW_eC_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    eC (∑ i ∈ s, a i) = ∏ i ∈ s, eC (a i) := by
  unfold eC
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- PROVED. The geometric sum over the symmetric range `|λ| ≤ L` of p. 246, display (6):
`|Σ_{|λ| ≤ L} e(γλ)| ≤ min(2L + 1, 1/(γ))`, from `karW_display6_geom` after the shift
`λ = m - (L + 1)`. -/
theorem karW_sym_geom (L : ℕ) (γ : ℝ) :
    ‖∑ x ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), eC (γ * (x : ℝ))‖ ≤
      karCapRecip ((2 * L + 1 : ℕ) : ℝ) γ := by
  have heq : ∑ m ∈ Finset.Icc 1 (2 * L + 1), eC (γ * (m : ℝ)) =
      ∑ x ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), eC (γ * ((L : ℝ) + 1)) * eC (γ * (x : ℝ)) := by
    apply Finset.sum_bij (fun (m : ℕ) _ => (m : ℤ) - (L + 1))
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m _ m' _ h
      omega
    · intro x hx
      refine ⟨(x + (L + 1)).toNat, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hx ⊢
        omega
      · simp only [Finset.mem_Icc] at hx
        omega
    · intro m _
      rw [← karW_eC_add]
      congr 1
      push_cast
      ring
  have h := karW_display6_geom (2 * L + 1) γ
  rw [heq, ← Finset.mul_sum, norm_mul, norm_eC, one_mul] at h
  exact h

/-- PROVED. The expansion of display (6), Karacuba p. 246: expand
`|Σ_y e(B_1 λ_1 y + ... + B_n λ_n y^n)|^{2k} = Σ_{u,v} e(Σ_s B_s λ_s μ_s(u, v))`,
`leafW_even_moment_expansion`, sum over the box `|λ_s| ≤ k P2^s`, factor the sum over `λ`
into `n` geometric sums of `2k P2^s + 1` terms and bound each by
`min(2kP2^s + 1, 1/(B_s μ_s))`, `karW_sym_geom`. -/
theorem karW_display6_expand (n M k : ℕ) (β : ℕ → ℝ) :
    ∑ lam ∈ karBox n k M, ‖karSy n M β lam‖ ^ (2 * k) ≤
      ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        ∏ j : Fin n, karCapRecip ((2 * (k * M ^ ((j : ℕ) + 1)) + 1 : ℕ) : ℝ)
          (β ((j : ℕ) + 1) * ((karPowVec n k M u - karPowVec n k M v) j : ℝ)) := by
  classical
  have hmom : ∀ lam : Fin n → ℤ, ‖karSy n M β lam‖ ^ (2 * k) =
      (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        ∏ j : Fin n, eC (β ((j : ℕ) + 1) * ((karPowVec n k M u - karPowVec n k M v) j : ℝ) *
          (lam j : ℝ))).re := by
    intro lam
    have h := congrArg Complex.re (leafW_even_moment_expansion
      (fun y : Fin (M + 1) =>
        ∑ j : Fin n, β ((j : ℕ) + 1) * (lam j : ℝ) * ((y : ℕ) : ℝ) ^ ((j : ℕ) + 1)) k)
    simp only [Complex.ofReal_re] at h
    unfold karSy
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [← karW_eC_sum]
    congr 1
    simp only [karPowVec, Pi.sub_apply]
    push_cast
    simp only [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  calc ∑ lam ∈ karBox n k M, ‖karSy n M β lam‖ ^ (2 * k)
      = (∑ lam ∈ karBox n k M, ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
          ∏ j : Fin n, eC (β ((j : ℕ) + 1) *
            ((karPowVec n k M u - karPowVec n k M v) j : ℝ) * (lam j : ℝ))).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun lam _ => hmom lam
    _ = (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
          ∏ j : Fin n, ∑ x ∈ Finset.Icc (-((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ))
              ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ),
            eC (β ((j : ℕ) + 1) *
              ((karPowVec n k M u - karPowVec n k M v) j : ℝ) * (x : ℝ))).re := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.prod_univ_sum, karBox]
    _ ≤ ‖∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
          ∏ j : Fin n, ∑ x ∈ Finset.Icc (-((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ))
              ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ),
            eC (β ((j : ℕ) + 1) *
              ((karPowVec n k M u - karPowVec n k M v) j : ℝ) * (x : ℝ))‖ := Complex.re_le_norm _
    _ ≤ ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
          ∏ j : Fin n, ‖∑ x ∈ Finset.Icc (-((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ))
              ((k * M ^ ((j : ℕ) + 1) : ℕ) : ℤ),
            eC (β ((j : ℕ) + 1) *
              ((karPowVec n k M u - karPowVec n k M v) j : ℝ) * (x : ℝ))‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
        exact le_of_eq (norm_prod _ _)
    _ ≤ _ := by
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => karW_sym_geom _ _)

/-- PROVED. The bound
of display (6), Karacuba p. 246, for the sum over the box:
`Σ_λ |Σ_y ...|^{2k} ≤ J_k(0) Π_{s=1}^n 𝔖_s`, by property a and c applied to
`F(μ) = Π_s min(2kP2^s + 1, 1/(B_s μ_s))` and the factorization of the sum over the box. -/
theorem karW_display6_box (n M k : ℕ) (β : ℕ → ℝ) :
    ∑ lam ∈ karBox n k M, ‖karSy n M β lam‖ ^ (2 * k) ≤
      karJ0 n k M * ∏ s ∈ Finset.Icc 1 n, karSigma k M s (β s) := by
  set F : (Fin n → ℤ) → ℝ := fun μ => ∏ j : Fin n,
    karCapRecip ((2 * (k * M ^ ((j : ℕ) + 1)) + 1 : ℕ) : ℝ) (β ((j : ℕ) + 1) * (μ j : ℝ)) with hF
  have hF0 : ∀ μ, 0 ≤ F μ := fun μ =>
    Finset.prod_nonneg fun j _ => karCapRecip_nonneg (by positivity) _
  have h1 := karW_display6_expand n M k β
  have h2 := karW_property_ac n k M F hF0
  have hbox : ∑ lam ∈ karBox n k M, F lam = ∏ s ∈ Finset.Icc 1 n, karSigma k M s (β s) := by
    rw [karW_prod_Icc_fin, karBox, hF]
    unfold karSigma
    rw [Finset.prod_univ_sum]

  rw [hbox] at h2
  exact h1.trans h2

/-- PROVED. Displays (5)
and (6) of Karacuba p. 245 last line to p. 246: `karW_display5_holder`, then property a and c,
then `karW_display6_box`:
`|W_1(a)|^{4k²} ≤ (P2+1)^{8k²-4k} J_k(0)² Π_{s=1}^n 𝔖_s`, for any real coefficients
`b = B_0`, `β s = B_s`. -/
theorem karW_display5_6 (n M k : ℕ) (hk : 1 ≤ k) (b : ℝ) (β : ℕ → ℝ) :
    ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      eC (b + ∑ j ∈ Finset.Icc 1 n, β j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (4 * k ^ 2)
      ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 n k M ^ 2 *
        ∏ s ∈ Finset.Icc 1 n, karSigma k M s (β s) := by
  have h1 := karW_display5_holder n M k hk b β
  have h2 := karW_property_ac n k M (fun lam => ‖karSy n M β lam‖ ^ (2 * k))
    (fun _ => by positivity)
  have h3 := karW_display6_box n M k β
  have hJ0 := karJ0_nonneg n k M
  have hm : 0 ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) := by positivity
  calc _ ≤ _ := h1
    _ ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) *
          (karJ0 n k M * ∑ lam ∈ karBox n k M, ‖karSy n M β lam‖ ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left h2 hm
    _ ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) *
          (karJ0 n k M * (karJ0 n k M * ∏ s ∈ Finset.Icc 1 n, karSigma k M s (β s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hJ0) hm
    _ = _ := by ring

/-! ### Lemma 1 for `J_k(0)`, p. 247 -/

/-- The binomial expansion of a shifted power sum. -/
theorem karW_shift_power_sum {k : ℕ} (x : Fin k → ℝ) (m : ℕ) :
    ∑ i : Fin k, (x i + 1) ^ m =
      ∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ) * ∑ i : Fin k, x i ^ t := by
  simp_rw [add_pow, one_pow, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- PROVED. The translation `y → y + 1` of Karacuba p. 247: a solution of the system
`Σ u_i^j = Σ v_i^j`, `j = 1, ..., n`, over `0, ..., M` gives one over `1, ..., M + 1`, so
`J_k(0)` over `0..P2` is at most the count over `1..P2+1` that Lemma 1 bounds. -/
theorem karJ0_le_shifted (n k M : ℕ) :
    karJ0 n k M ≤
      ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        if (∀ j : Fin n,
          (∑ i : Fin k, (((u i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) -
            (∑ i : Fin k, (((v i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) = (fun _ => (0 : ℝ)) j)
          then (1 : ℝ) else 0 := by
  unfold karJ0
  refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
  by_cases h : ∀ j : Fin n, ∑ i : Fin k, ((u i : ℕ) : ℝ) ^ ((j : ℕ) + 1) =
      ∑ i : Fin k, ((v i : ℕ) : ℝ) ^ ((j : ℕ) + 1)
  · have h' : ∀ j : Fin n,
        (∑ i : Fin k, (((u i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) -
          (∑ i : Fin k, (((v i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) = (fun _ => (0 : ℝ)) j := by
      intro j
      simp only [Nat.cast_add, Nat.cast_one]
      rw [karW_shift_power_sum (fun i => ((u i : ℕ) : ℝ)),
        karW_shift_power_sum (fun i => ((v i : ℕ) : ℝ)), sub_eq_zero]
      refine Finset.sum_congr rfl fun t ht => ?_
      congr 1
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0; simp
      · have htm : t ≤ (j : ℕ) + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
        have htn : t - 1 < n := by omega
        have := h ⟨t - 1, htn⟩
        simp only at this
        rwa [Nat.sub_add_cancel hpos] at this
    rw [if_pos h, if_pos h']
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- PROVED CONDITIONAL ON KarLemma1. Karacuba p. 247: Lemma 1 with `b = k = b_l`, `n ≥ 12`,
for `J_k(0)` over `0, ..., P2`, through the translation `karJ0_le_shifted` and the proved
`leafW_shifted_solution_bound` at the zero vector:
`J_k(0) < D_l (P2+1)^{2k - n(n+1)/2 + n(n+1)/2 (1-1/n)^l}`. -/
theorem karJ0_lemma1 (h1 : KarLemma1) (n l M : ℕ) (hn : 12 ≤ n) (hl : 0 < l) :
    karJ0 n (n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M <
      (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        ((M : ℝ) + 1) ^ ((2 * ((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) : ℝ)
          - ((n * (n + 1) : ℕ) : ℝ) / 2 + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  have h := leafW_shifted_solution_bound h1 n l (M + 1) hn hl (Nat.succ_pos M)
    (fun _ => (0 : ℝ))
  simp only at h
  have hc : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  rw [hc] at h
  exact lt_of_le_of_lt (karJ0_le_shifted n _ M) h

/-! ### Display (7), p. 247 -/

/-- PROVED. The trivial bound of Karacuba p. 247 for `s` not among `s_1, ..., s_r`:
`𝔖_s ≤ (2kP2^s + 1)² ≤ 9k² (P2+1)^{2s}`; the paper writes `5k² P2^{2s}`. -/
theorem karSigma_trivial (k M s : ℕ) (hk : 1 ≤ k) (β : ℝ) :
    karSigma k M s β ≤ 9 * (k : ℝ) ^ 2 * ((M : ℝ) + 1) ^ (2 * s) := by
  unfold karSigma
  set L : ℕ := k * M ^ s with hL
  have hterm : ∀ μ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      karCapRecip ((2 * L + 1 : ℕ) : ℝ) (β * μ) ≤ ((2 * L + 1 : ℕ) : ℝ) := by
    intro μ _
    unfold karCapRecip
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]; omega
  have h1 := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [hcard, nsmul_eq_mul] at h1
  have hU : ((2 * L + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) * ((M : ℝ) + 1) ^ s := by
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hMs : (M : ℝ) ^ s ≤ ((M : ℝ) + 1) ^ s :=
      pow_le_pow_left₀ (by positivity) (by linarith) s
    have h1s : (1 : ℝ) ≤ ((M : ℝ) + 1) ^ s := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) M])
    have : (1 : ℝ) ≤ (k : ℝ) * ((M : ℝ) + 1) ^ s := by nlinarith
    rw [hL]; push_cast
    nlinarith
  have hU0 : (0 : ℝ) ≤ ((2 * L + 1 : ℕ) : ℝ) := by positivity
  calc _ ≤ ((2 * L + 1 : ℕ) : ℝ) * ((2 * L + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (3 * (k : ℝ) * ((M : ℝ) + 1) ^ s) * (3 * (k : ℝ) * ((M : ℝ) + 1) ^ s) :=
        mul_le_mul hU hU hU0 (le_trans hU0 hU)
    _ = 9 * (k : ℝ) ^ 2 * ((M : ℝ) + 1) ^ (2 * s) := by rw [pow_mul']; ring

/-- `2 (1 + ... + n) = n(n+1)`. -/
theorem karW_two_sum_Icc (n : ℕ) : 2 * ∑ s ∈ Finset.Icc 1 n, s = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

/-- PROVED. The product over `s = 1, ..., n` after display (7), Karacuba p. 247: from the
bound of each factor `𝔖_{s_j}` and the trivial bound of the others,
`𝔖 ≤ 4^{n(n+1)} (30k²)^n (9n)^n (log P)^n (P2+1)^{n(n+1)} P^{-ρ(s_1 + ... + s_r)}`. -/
theorem karW_sigma_product {n k : ℕ} {T : Finset ℕ} {F : ℕ → ℝ} {m P Lg ρ : ℝ}
    (hn : 1 ≤ n) (hT : T ⊆ Finset.Icc 2 n) (hF0 : ∀ s, 0 ≤ F s) (hm : 1 ≤ m) (hP : 0 < P)
    (hLg : 1 ≤ Lg)
    (hTb : ∀ s ∈ T, F s ≤ (16 : ℝ) ^ s * (30 * (k : ℝ) ^ 2 * (9 * (n : ℝ)) * Lg) *
      m ^ (2 * s) * P ^ (-(ρ * s)))
    (hNb : ∀ s, F s ≤ 9 * (k : ℝ) ^ 2 * m ^ (2 * s)) :
    ∏ s ∈ Finset.Icc 1 n, F s ≤ (4 : ℝ) ^ (n * (n + 1)) * (30 * (k : ℝ) ^ 2) ^ n *
      (9 * (n : ℝ)) ^ n * Lg ^ n * m ^ (n * (n + 1)) * P ^ (-(ρ * ∑ s ∈ T, (s : ℝ))) := by
  classical
  set K : ℝ := 30 * (k : ℝ) ^ 2 * (9 * (n : ℝ)) * Lg with hK
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hG : ∀ s ∈ Finset.Icc 1 n, F s ≤
      (16 : ℝ) ^ s * K * m ^ (2 * s) * (if s ∈ T then P ^ (-(ρ * s)) else 1) := by
    intro s _
    by_cases hs : s ∈ T
    · rw [if_pos hs]; exact hTb s hs
    · rw [if_neg hs, mul_one]
      refine (hNb s).trans ?_
      have h16 : (1 : ℝ) ≤ (16 : ℝ) ^ s := one_le_pow₀ (by norm_num)
      have hK9 : 9 * (k : ℝ) ^ 2 ≤ K := by
        rw [hK]
        have : (9 : ℝ) ≤ 30 * (9 * (n : ℝ)) * Lg := by nlinarith
        nlinarith [sq_nonneg (k : ℝ)]
      have hms : 0 ≤ m ^ (2 * s) := by positivity
      have hK0 : 0 ≤ K := le_trans (by positivity) hK9
      calc 9 * (k : ℝ) ^ 2 * m ^ (2 * s) ≤ 1 * K * m ^ (2 * s) := by nlinarith
        _ ≤ _ := by gcongr
  have hle := Finset.prod_le_prod₀ (fun s _ => hF0 s) hG
  refine hle.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    Finset.prod_ite_mem, Nat.card_Icc]
  have hTI : Finset.Icc 1 n ∩ T = T := by
    apply Finset.inter_eq_right.mpr
    intro s hs
    have := Finset.mem_Icc.mp (hT hs)
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  rw [hTI, ← Real.rpow_sum_of_pos hP]
  have hsum2 : ∑ i ∈ Finset.Icc 1 n, 2 * i = n * (n + 1) := by
    rw [← Finset.mul_sum]; exact karW_two_sum_Icc n
  have h16 : (16 : ℝ) ^ (∑ i ∈ Finset.Icc 1 n, i) = (4 : ℝ) ^ (n * (n + 1)) := by
    rw [← karW_two_sum_Icc n, pow_mul]; norm_num
  have hneg : ∑ i ∈ T, -(ρ * (i : ℝ)) = -(ρ * ∑ s ∈ T, (s : ℝ)) := by
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  rw [hsum2, h16, hneg, Nat.add_sub_cancel, hK, mul_pow, mul_pow]
  ring

/-- PROVED. The arithmetic of p. 247 after display (7) for one factor:
`Q^{-1} + P2^{-s} log Q + P2^{-2s} Q log Q ≤ 16^s · 9n log P · P^{-ρ s}` from
`Q^{-1} ≤ 2P^{-c3 s}`, `P2^{-s} ≤ 2^s P^{-c1 s/3}`, `P2^{-2s} Q ≤ 4^s P^{-c4 s}`,
`0 ≤ log Q ≤ n log P` and `P^{-c s} ≤ P^{-ρ s}`; the paper writes `9n P^{-ρ s} log P`. -/
theorem karW_factor_sum_le {q X lq Lg p1 p3 p4 pr nn : ℝ} (s : ℕ)
    (hq : 1 / q ≤ 2 * p3) (hX : X⁻¹ ≤ (2 : ℝ) ^ s * p1) (hXX : (X ^ 2)⁻¹ * q ≤ (4 : ℝ) ^ s * p4)
    (hlq0 : 0 ≤ lq) (hlq : lq ≤ nn * Lg) (hLg : 1 ≤ Lg) (hnn : 1 ≤ nn)
    (h1 : p1 ≤ pr) (h3 : p3 ≤ pr) (h4 : p4 ≤ pr) (hp1 : 0 ≤ p1) (hp4 : 0 ≤ p4)
    (hX0 : 0 ≤ X⁻¹) (hXX0 : 0 ≤ (X ^ 2)⁻¹ * q) :
    1 / q + X⁻¹ * lq + (X ^ 2)⁻¹ * q * lq ≤ (16 : ℝ) ^ s * (9 * nn) * Lg * pr := by
  have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have h4s : (4 : ℝ) ^ s = (2 : ℝ) ^ s * (2 : ℝ) ^ s := by rw [← mul_pow]; norm_num
  have h16s : (16 : ℝ) ^ s = (4 : ℝ) ^ s * (4 : ℝ) ^ s := by rw [← mul_pow]; norm_num
  have h4s1 : (1 : ℝ) ≤ (4 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have hpr : 0 ≤ pr := le_trans hp1 h1
  have hnL : 1 ≤ nn * Lg := by nlinarith
  have hA : 1 / q ≤ 2 * pr * (nn * Lg) := by nlinarith
  have hB : X⁻¹ * lq ≤ (2 : ℝ) ^ s * pr * (nn * Lg) := by
    have : X⁻¹ ≤ (2 : ℝ) ^ s * pr := le_trans hX (by nlinarith)
    calc X⁻¹ * lq ≤ ((2 : ℝ) ^ s * pr) * (nn * Lg) :=
          mul_le_mul this hlq hlq0 (le_trans hX0 this)
      _ = _ := by ring
  have hC : (X ^ 2)⁻¹ * q * lq ≤ (4 : ℝ) ^ s * pr * (nn * Lg) := by
    have : (X ^ 2)⁻¹ * q ≤ (4 : ℝ) ^ s * pr := le_trans hXX (by nlinarith)
    calc (X ^ 2)⁻¹ * q * lq ≤ ((4 : ℝ) ^ s * pr) * (nn * Lg) :=
          mul_le_mul this hlq hlq0 (le_trans hXX0 this)
      _ = _ := by ring
  have hsum : 2 + (2 : ℝ) ^ s + (4 : ℝ) ^ s ≤ 9 * (16 : ℝ) ^ s := by
    rw [h16s, h4s] at *; nlinarith
  have hfin : (2 + (2 : ℝ) ^ s + (4 : ℝ) ^ s) * (pr * (nn * Lg)) ≤
      9 * (16 : ℝ) ^ s * (pr * (nn * Lg)) :=
    mul_le_mul_of_nonneg_right hsum (by positivity)
  nlinarith

/-- PROVED. The choice `n ≥ n0 ≥ 1/∛(c1 - (c2 + c4))` of p. 245 gives
`1/(n²(n+1)) ≤ c1 - (c2 + c4)`, used on p. 247 for `P2^{-2} P^{c2} ≤ 4P^{-c4}`. -/
theorem karW_n0_cube {c1 c2 c4 : ℝ} {n : ℕ} (hd : c2 + c4 < c1) (hn : karN0 c1 c2 c4 ≤ n) :
    1 / ((n : ℝ) ^ 2 * (n + 1)) ≤ c1 - (c2 + c4) := by
  set d := c1 - (c2 + c4) with hdd
  have hd0 : 0 < d := by rw [hdd]; linarith
  have hcube : 1 / d ^ ((1 : ℝ) / 3) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hr0 : 0 < d ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hd0 _
  have h1 : 1 ≤ (n : ℝ) * d ^ ((1 : ℝ) / 3) := (div_le_iff₀ hr0).mp hcube
  have h3 : 1 ≤ ((n : ℝ) * d ^ ((1 : ℝ) / 3)) ^ 3 := one_le_pow₀ h1
  have hd3 : (d ^ ((1 : ℝ) / 3)) ^ 3 = d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le]; norm_num
  rw [mul_pow, hd3] at h3
  have hn1 : (1 : ℝ) ≤ n := by
    have : (12 : ℝ) ≤ n := le_trans (le_max_left _ _) hn
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 * (n + 1) := by positivity
  rw [div_le_iff₀ hpos]
  have : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * (n + 1) := by nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- PROVED. Display (7) of Karacuba p. 247 for one factor `s = s_j`: hypothesis b of
`KarHyp` at `x = a` gives `P^{-c2 s} ≤ |B_s| ≤ P^{-c3 s}`, so
`B_s = a_s/Q_s + θ_s/Q_s²` with `Q_s = [|B_s|^{-1}]`, `Decomp538a.signed_reciprocal_floor_approx`;
Lemma 3 on the symmetric range, `Decomp538a.signed_interval_reciprocal_bound`, and
`Decomp538a.karacuba_factor_thirty` for `k ≥ 7` give
`𝔖_s ≤ 30 k² P2^{2s} (Q_s^{-1} + P2^{-s} log Q_s + P2^{-2s} Q_s log Q_s)`; then
`Q_s^{-1} ≤ 2P^{-c3 s}`, `P2^{-1} ≤ 2P^{-c1/3}`, `P2^{-2} P^{c2} ≤ 4 P^{-c4}` by the choice of
`n0`, and `log Q_s ≤ n log P`, `karW_factor_sum_le`. The `16^s` holds the slips `2^s`, `4^s`
of the paper. -/
theorem karW_display7_factor :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ cc0 : ℝ, 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a k s : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a ≤ N + P → 7 ≤ k → s ∈ T →
          karSigma k (karP2 c1 n P) s (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ))
            ≤ (16 : ℝ) ^ s * (30 * (k : ℝ) ^ 2 * (9 * (n : ℝ)) * Real.log (P : ℝ)) *
              ((karP2 c1 n P : ℝ) + 1) ^ (2 * s) *
              (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (s : ℝ))) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  refine ⟨1, one_pos, ?_⟩
  intro N P n f T a k s hP hn hn0 hbig hH ha haP hk hs
  obtain ⟨_, _, hT, _, hB⟩ := hH
  have hsI := Finset.mem_Icc.mp (hT hs)
  have hPr1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsr : (2 : ℝ) ≤ s := by exact_mod_cast hsI.1
  have hsn : (s : ℝ) ≤ n := by exact_mod_cast hsI.2
  have hkr : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hLg : 1 ≤ Real.log (P : ℝ) := by
    have h1 : Real.exp 1 ≤ P := by
      refine le_trans (Real.exp_le_exp.2 ?_) hbig
      nlinarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have haI : (a : ℝ) ∈ Set.Icc (N : ℝ) (N + P) := by
    constructor
    · exact_mod_cast ha
    · exact_mod_cast haP
  obtain ⟨hlo, hhi⟩ := hB s hs (a : ℝ) haI
  set b := iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) with hbdef
  have hbpos : 0 < |b| := lt_of_lt_of_le (Real.rpow_pos_of_pos hPpos _) hlo
  have hb0 : b ≠ 0 := abs_pos.mp hbpos
  have hc3le : (P : ℝ) ^ (-(c3 * s)) ≤ 1 := by
    rw [← Real.rpow_zero (P : ℝ)]
    have : 0 ≤ c3 * s := by positivity
    exact Real.rpow_le_rpow_of_exponent_le hPr1 (by linarith)
  have hb1 : |b| ≤ 1 := le_trans hhi hc3le
  obtain ⟨hq1, _, hqle, a', θ, hgcd, hθ, hbeq⟩ :=
    LeanLab.ExceptionalSet.Decomp538a.signed_reciprocal_floor_approx b hb0 hb1
  set q : ℕ := ⌊|b|⁻¹⌋₊ with hqdef
  set M : ℕ := karP2 c1 n P with hM
  -- Lemma 3
  have hL3 := LeanLab.ExceptionalSet.Decomp538a.signed_interval_reciprocal_bound
    ((2 * (k * M ^ s) + 1 : ℕ) : ℝ) (k * M ^ s) a' q θ 0 (by positivity) hq1 hgcd hθ
  simp only [add_zero] at hL3
  have hS1 : karSigma k M s b ≤ 6 * (((2 * (k * M ^ s) + 1 : ℕ) : ℝ) + q * Real.log q) *
      (((2 * (k * M ^ s) + 1 : ℕ) : ℝ) / q + 1) := by
    unfold karSigma karCapRecip nint
    rw [hbeq]
    exact hL3
  -- the size of `P2`
  have hscale : 1 ≤ c1 * (n : ℝ) ^ 2 :=
    LeanLab.ExceptionalSet.Decomp538a.karacuba_large_order_scale c1 n hc1
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn0)
  have hfl := LeanLab.ExceptionalSet.Decomp538a.karacuba_shift_floor_bounds c1 n P hc1 hn hP hscale
  have hM1 : 1 ≤ M := hfl.1
  have hMinv : (1 : ℝ) / M ≤ 2 * (P : ℝ) ^ (-(c1 / 3)) := hfl.2
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set X : ℝ := (M : ℝ) ^ s with hX
  have hX1 : 1 ≤ X := one_le_pow₀ hMr
  have h30 := LeanLab.ExceptionalSet.Decomp538a.karacuba_factor_thirty (k : ℝ) X q hkr hX1 hq1
  have hcastU : ((2 * (k * M ^ s) + 1 : ℕ) : ℝ) = 2 * (k : ℝ) * X + 1 := by
    rw [hX]; push_cast; ring
  rw [hcastU] at hS1
  have hS2 := hS1.trans h30
  -- the three ratios
  have hqinv : 1 / (q : ℝ) ≤ 2 * (P : ℝ) ^ (-(c3 * s)) := by
    have := LeanLab.ExceptionalSet.Decomp538a.reciprocal_floor_inverse_bound |b| hbpos hb1
    linarith
  have hqP : (q : ℝ) ≤ (P : ℝ) ^ (c2 * s) := by
    refine le_trans hqle ?_
    have := (inv_le_inv₀ hbpos (Real.rpow_pos_of_pos hPpos _)).mpr hlo
    rwa [Real.rpow_neg hPpos.le, inv_inv] at this
  have hqr1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hqr1
  have hlq : Real.log q ≤ (n : ℝ) * Real.log P := by
    have h1 := Real.log_le_log (by linarith) hqP
    rw [Real.log_rpow hPpos] at h1
    have hlogP0 : 0 ≤ Real.log (P : ℝ) := by linarith
    have hc21 : c2 ≤ 1 := by linarith
    have h2 : c2 * s ≤ n := by
      have := mul_le_mul_of_nonneg_right hc21 (by linarith : (0 : ℝ) ≤ s)
      linarith
    have := mul_le_mul_of_nonneg_right h2 hlogP0
    linarith
  have hXinv : X⁻¹ ≤ (2 : ℝ) ^ s * (P : ℝ) ^ (-(c1 / 3 * s)) := by
    have hM0 : (0 : ℝ) < M := by linarith
    have : X⁻¹ = (1 / (M : ℝ)) ^ s := by rw [hX, one_div, inv_pow]
    rw [this]
    calc (1 / (M : ℝ)) ^ s ≤ (2 * (P : ℝ) ^ (-(c1 / 3))) ^ s :=
          pow_le_pow_left₀ (by positivity) hMinv s
      _ = (2 : ℝ) ^ s * (P : ℝ) ^ (-(c1 / 3 * s)) := by
          rw [mul_pow, ← Real.rpow_natCast ((P : ℝ) ^ _), ← Real.rpow_mul hPpos.le]
          congr 2; ring
  -- `1/P2 ≤ 2 P^{-e}`
  set e : ℝ := c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) with he
  have hMe : (1 : ℝ) / M ≤ 2 * (P : ℝ) ^ (-e) := by
    have hb' : 0 < (P : ℝ) ^ (-e) := Real.rpow_pos_of_pos hPpos _
    have he0 : 0 ≤ e := by
      have hd : (0 : ℝ) < 2 * ((n : ℝ) ^ 2 * (n + 1)) := by positivity
      have hm := mul_le_mul_of_nonneg_right hscale (by positivity : (0 : ℝ) ≤ n + 1)
      have hi : 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) ≤ c1 / 2 := by
        apply (div_le_iff₀ hd).mpr
        have e1 : c1 / 2 * (2 * ((n : ℝ) ^ 2 * (n + 1))) = c1 * (n : ℝ) ^ 2 * (n + 1) := by ring
        have hn1 : (1 : ℝ) ≤ n + 1 := by linarith
        rw [e1]; linarith
      rw [he]; linarith
    have hb1' : (P : ℝ) ^ (-e) ≤ 1 := by
      rw [← Real.rpow_zero (P : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hPr1 (by linarith)
    have := LeanLab.ExceptionalSet.Decomp538a.reciprocal_floor_inverse_bound _ hb' hb1'
    have hinv : ((P : ℝ) ^ (-e))⁻¹ = (P : ℝ) ^ e := by rw [Real.rpow_neg hPpos.le, inv_inv]
    have hMdef : M = ⌊(P : ℝ) ^ e⌋₊ := by rw [hM, karP2]
    rw [hinv] at this
    rw [hMdef]; exact this
  have hcube := karW_n0_cube hc241 hn0
  have h2e : c2 - 2 * e ≤ -c4 := by
    rw [he]
    have : 2 * (1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))) = 1 / ((n : ℝ) ^ 2 * (n + 1)) := by
      field_simp
    linarith
  have hXX : (X ^ 2)⁻¹ * q ≤ (4 : ℝ) ^ s * (P : ℝ) ^ (-(c4 * s)) := by
    have hM0 : (0 : ℝ) < M := by linarith
    have h1 : (X ^ 2)⁻¹ = ((1 / (M : ℝ)) ^ 2) ^ s := by
      rw [hX, ← pow_mul, ← pow_mul, one_div, inv_pow, mul_comm s 2]
    have h2 : ((1 / (M : ℝ)) ^ 2) ^ s ≤ ((2 * (P : ℝ) ^ (-e)) ^ 2) ^ s :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hMe 2) s
    have h3 : ((2 * (P : ℝ) ^ (-e)) ^ 2) ^ s * (P : ℝ) ^ (c2 * s)
        = (4 : ℝ) ^ s * (P : ℝ) ^ ((c2 - 2 * e) * s) := by
      rw [← pow_mul, mul_pow, show (2 : ℝ) ^ (2 * s) = 4 ^ s by rw [pow_mul]; norm_num,
        ← Real.rpow_natCast ((P : ℝ) ^ (-e)) (2 * s), ← Real.rpow_mul hPpos.le, mul_assoc,
        ← Real.rpow_add hPpos]
      congr 2
      push_cast; ring
    have h4 : (P : ℝ) ^ ((c2 - 2 * e) * s) ≤ (P : ℝ) ^ (-(c4 * s)) :=
      Real.rpow_le_rpow_of_exponent_le hPr1
        (by have := mul_le_mul_of_nonneg_right h2e (by linarith : (0 : ℝ) ≤ s); linarith)
    rw [h1]
    calc ((1 / (M : ℝ)) ^ 2) ^ s * q ≤ ((2 * (P : ℝ) ^ (-e)) ^ 2) ^ s * (P : ℝ) ^ (c2 * s) :=
          mul_le_mul h2 hqP (by positivity) (by positivity)
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  -- `P^{-c s} ≤ P^{-ρ s}`
  set ρ := min (c1 / 3) (min c3 c4) with hρ
  have hρ1 : ρ ≤ c1 / 3 := min_le_left _ _
  have hρ3 : ρ ≤ c3 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ c4 := (min_le_right _ _).trans (min_le_right _ _)
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hp1 : (P : ℝ) ^ (-(c1 / 3 * s)) ≤ (P : ℝ) ^ (-(ρ * s)) :=
    Real.rpow_le_rpow_of_exponent_le hPr1
      (by have := mul_le_mul_of_nonneg_right hρ1 hs0; linarith)
  have hp3 : (P : ℝ) ^ (-(c3 * s)) ≤ (P : ℝ) ^ (-(ρ * s)) :=
    Real.rpow_le_rpow_of_exponent_le hPr1
      (by have := mul_le_mul_of_nonneg_right hρ3 hs0; linarith)
  have hp4 : (P : ℝ) ^ (-(c4 * s)) ≤ (P : ℝ) ^ (-(ρ * s)) :=
    Real.rpow_le_rpow_of_exponent_le hPr1
      (by have := mul_le_mul_of_nonneg_right hρ4 hs0; linarith)
  have hF := karW_factor_sum_le s hqinv hXinv hXX hlq0 hlq hLg (by linarith) hp1 hp3 hp4
    (Real.rpow_nonneg hPpos.le _) (Real.rpow_nonneg hPpos.le _)
    (inv_nonneg.mpr (by positivity)) (by positivity)
  have hXM : X ^ 2 ≤ ((M : ℝ) + 1) ^ (2 * s) := by
    rw [hX, ← pow_mul, mul_comm]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hF0 : 0 ≤ 1 / (q : ℝ) + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q := by
    have : 0 ≤ X⁻¹ := inv_nonneg.mpr (by positivity)
    have : 0 ≤ (X ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
    positivity
  calc karSigma k M s b ≤ 30 * (k : ℝ) ^ 2 * X ^ 2 *
        (1 / (q : ℝ) + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := hS2
    _ ≤ 30 * (k : ℝ) ^ 2 * ((M : ℝ) + 1) ^ (2 * s) *
        ((16 : ℝ) ^ s * (9 * (n : ℝ)) * Real.log P * (P : ℝ) ^ (-(ρ * s))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hXM (by positivity)) hF hF0 (by positivity)
    _ = _ := by ring

/-- PROVED. Display (7) of Karacuba p. 247 and the
estimate of `𝔖` after it: the factors `s = s_j` from `karW_display7_factor`, the others
from `karSigma_trivial`, the product from `karW_sigma_product`; the slips `2^s`, `4^s` of the
paper and the change `P2 → P2 + 1` are absorbed by `4^{n(n+1)}`. -/
theorem karW_display7 (h3 : KarLemma3) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ cc0 : ℝ, 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a k : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a ≤ N + P → 7 ≤ k →
          ∏ s ∈ Finset.Icc 1 n,
              karSigma k (karP2 c1 n P) s (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ))
            ≤ (4 : ℝ) ^ (n * (n + 1)) * (30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n *
              (Real.log (P : ℝ)) ^ n * ((karP2 c1 n P : ℝ) + 1) ^ (n * (n + 1)) *
              (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)))) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  obtain ⟨cc0, hcc0, hfac⟩ :=
    karW_display7_factor c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  refine ⟨max cc0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro N P n f T a k hP hn hn0 hbig hH ha haP hk
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hbig' : Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P :=
    le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      hbig
  have hLg : 1 ≤ Real.log (P : ℝ) := by
    have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
    have h1 : Real.exp 1 ≤ P := by
      refine le_trans (Real.exp_le_exp.2 ?_) hbig
      have := le_max_right cc0 1
      nlinarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hHc := hH
  obtain ⟨_, _, hT, _, _⟩ := hHc
  have hm : (1 : ℝ) ≤ (karP2 c1 n P : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (karP2 c1 n P); linarith
  have h := karW_sigma_product (n := n) (k := k) (T := T)
    (F := fun s => karSigma k (karP2 c1 n P) s (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ)))
    (m := (karP2 c1 n P : ℝ) + 1) (P := (P : ℝ)) (Lg := Real.log (P : ℝ))
    (ρ := min (c1 / 3) (min c3 c4)) (by omega) hT (fun s => karSigma_nonneg _ _ _ _) hm
    (by exact_mod_cast hP) hLg
    (fun s hs => hfac N P n f T a k s hP hn hn0 hbig' hH ha haP hk hs)
    (fun s => karSigma_trivial k _ s (by omega) _)
  exact h

/-! ### Bookkeeping for display (8), p. 247 -/

/-- PROVED. The powers of `P2 + 1` on p. 247: `(P2+1)^{8k²-4k} ((P2+1)^{E1})² (P2+1)^{n(n+1)}
= (P2+1)^{8k²} (P2+1)^{n(n+1)(1-1/n)^l}` for `E1 = 2k - n(n+1)/2 + n(n+1)/2 (1-1/n)^l`. -/
theorem karW_pow_m (m q : ℝ) (hm : 0 < m) (k A l : ℕ) (hk : 1 ≤ k) :
    m ^ (8 * k ^ 2 - 4 * k) * (m ^ (2 * (k : ℝ) - (A : ℝ) / 2 + (A : ℝ) / 2 * q ^ l)) ^ 2 * m ^ A
      = m ^ (8 * k ^ 2) * m ^ ((A : ℝ) * q ^ l) := by
  have h48 : 4 * k ≤ 8 * k ^ 2 := by nlinarith
  rw [← Real.rpow_natCast m (8 * k ^ 2 - 4 * k), ← Real.rpow_natCast (m ^ _) 2,
    ← Real.rpow_mul hm.le, ← Real.rpow_natCast m A, ← Real.rpow_natCast m (8 * k ^ 2),
    ← Real.rpow_add hm, ← Real.rpow_add hm, ← Real.rpow_add hm]
  congr 1
  push_cast [Nat.cast_sub h48]
  ring

/-- PROVED. `D_l² = (20n)^{n(n+1)l}`, p. 247. -/
theorem karW_D_sq (n l : ℕ) :
    ((20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l)) ^ 2 = (20 * (n : ℝ)) ^ (n * (n + 1) * l) := by
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast _ (n * (n + 1) * l)]
  congr 1
  push_cast; ring

/-- PROVED. The factor `(P2+1)^{n(n+1)(1-1/n)^l}` of p. 247: from `P2 + 1 ≤ 2P^e`, `e ≤ 1/2`,
`0 ≤ x ≤ n(n+1)` and `x ≤ ρ(s_1 + ... + s_r)` it is at most `2^{n(n+1)} P^{ρ(s_1+...+s_r)/2}`;
the paper writes `P2^{n(n+1)(1-1/n)^l} ≤ P^{0.5ρ(s_1+...+s_r)}`. -/
theorem karW_m_pow_x {m P e x s : ℝ} {A : ℕ} (hm : 0 ≤ m) (hP1 : 1 ≤ P) (hm2 : m ≤ 2 * P ^ e)
    (he : e ≤ 1 / 2) (hx0 : 0 ≤ x) (hxA : x ≤ A) (hxs : x ≤ s) :
    m ^ x ≤ (2 : ℝ) ^ A * P ^ (s / 2) := by
  have hP0 : 0 ≤ P := by linarith
  have hex : e * x ≤ s / 2 := by nlinarith
  calc m ^ x ≤ (2 * P ^ e) ^ x := Real.rpow_le_rpow hm hm2 hx0
    _ = (2 : ℝ) ^ x * P ^ (e * x) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hP0 _), ← Real.rpow_mul hP0]
    _ ≤ (2 : ℝ) ^ (A : ℝ) * P ^ (s / 2) := by
        apply mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hxA)
          (Real.rpow_le_rpow_of_exponent_le hP1 hex) (Real.rpow_nonneg hP0 _) (by positivity)
    _ = (2 : ℝ) ^ A * P ^ (s / 2) := by rw [Real.rpow_natCast]

/-- PROVED. The combination of p. 247 before display (8):
`|W_1|^{4k²} ≤ (P2+1)^{8k²-4k} J_k(0)² 𝔖`, `J_k(0) ≤ D_l (P2+1)^{E1}` and
`𝔖 ≤ 4^{n(n+1)} C (P2+1)^{n(n+1)} P^{-ρσ}` give `|W_1|^{4k²} ≤ 8^{4k²} D_l² C (P2+1)^{8k²} P^{-ρσ/2}`. -/
theorem karW_combine {X J Sg D C m P E1 x s : ℝ} {A k : ℕ} (hm : 0 < m) (hP : 0 < P)
    (hJ0 : 0 ≤ J) (hSg0 : 0 ≤ Sg) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) (hAk : A ≤ 4 * k ^ 2)
    (h56 : X ^ (4 * k ^ 2) ≤ m ^ (8 * k ^ 2 - 4 * k) * J ^ 2 * Sg)
    (hJ : J ≤ D * m ^ E1)
    (hS : Sg ≤ (4 : ℝ) ^ A * C * m ^ A * P ^ (-s))
    (hpow : m ^ (8 * k ^ 2 - 4 * k) * (m ^ E1) ^ 2 * m ^ A = m ^ (8 * k ^ 2) * m ^ x)
    (hmx : m ^ x ≤ (2 : ℝ) ^ A * P ^ (s / 2)) :
    X ^ (4 * k ^ 2) ≤ (8 : ℝ) ^ (4 * k ^ 2) * (D ^ 2 * C) * m ^ (8 * k ^ 2) * P ^ (-(s / 2)) := by
  have hJ2 : J ^ 2 ≤ (D * m ^ E1) ^ 2 := pow_le_pow_left₀ hJ0 hJ 2
  have hm8 : 0 ≤ m ^ (8 * k ^ 2 - 4 * k) := by positivity
  have hPs : 0 ≤ P ^ (-s) := Real.rpow_nonneg hP.le _
  have hmx0 : 0 ≤ m ^ x := Real.rpow_nonneg hm.le _
  have hK : 0 ≤ D ^ 2 * (4 : ℝ) ^ A * C * m ^ (8 * k ^ 2) := by positivity
  have hstep1 : m ^ (8 * k ^ 2 - 4 * k) * J ^ 2 * Sg ≤
      m ^ (8 * k ^ 2 - 4 * k) * (D * m ^ E1) ^ 2 * ((4 : ℝ) ^ A * C * m ^ A * P ^ (-s)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hJ2 hm8) hS hSg0 (by positivity)
  have heq : m ^ (8 * k ^ 2 - 4 * k) * (D * m ^ E1) ^ 2 * ((4 : ℝ) ^ A * C * m ^ A * P ^ (-s))
      = D ^ 2 * (4 : ℝ) ^ A * C * (m ^ (8 * k ^ 2 - 4 * k) * (m ^ E1) ^ 2 * m ^ A) * P ^ (-s) := by
    ring
  have hstep2 : D ^ 2 * (4 : ℝ) ^ A * C * (m ^ (8 * k ^ 2) * m ^ x) * P ^ (-s) ≤
      D ^ 2 * (4 : ℝ) ^ A * C * (m ^ (8 * k ^ 2) * ((2 : ℝ) ^ A * P ^ (s / 2))) * P ^ (-s) := by
    have : D ^ 2 * (4 : ℝ) ^ A * C * (m ^ (8 * k ^ 2) * m ^ x) ≤
        D ^ 2 * (4 : ℝ) ^ A * C * (m ^ (8 * k ^ 2) * ((2 : ℝ) ^ A * P ^ (s / 2))) := by
      have h := mul_le_mul_of_nonneg_left hmx hK
      linarith [h]
    exact mul_le_mul_of_nonneg_right this hPs
  have hPP : P ^ (s / 2) * P ^ (-s) = P ^ (-(s / 2)) := by
    rw [← Real.rpow_add hP]; congr 1; ring
  have heq2 : D ^ 2 * (4 : ℝ) ^ A * C * (m ^ (8 * k ^ 2) * ((2 : ℝ) ^ A * P ^ (s / 2))) * P ^ (-s)
      = (8 : ℝ) ^ A * (D ^ 2 * C) * m ^ (8 * k ^ 2) * P ^ (-(s / 2)) := by
    rw [← hPP, show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]; ring
  have h8 : (8 : ℝ) ^ A ≤ (8 : ℝ) ^ (4 * k ^ 2) := pow_le_pow_right₀ (by norm_num) hAk
  have hrest : 0 ≤ (D ^ 2 * C) * m ^ (8 * k ^ 2) * P ^ (-(s / 2)) := by
    have := Real.rpow_nonneg hP.le (-(s / 2)); positivity
  calc X ^ (4 * k ^ 2) ≤ _ := h56
    _ ≤ _ := hstep1
    _ = _ := heq
    _ = D ^ 2 * (4 : ℝ) ^ A * C * (m ^ (8 * k ^ 2) * m ^ x) * P ^ (-s) := by rw [hpow]
    _ ≤ _ := hstep2
    _ = _ := heq2
    _ ≤ (8 : ℝ) ^ (4 * k ^ 2) * (D ^ 2 * C) * m ^ (8 * k ^ 2) * P ^ (-(s / 2)) := by
        have := mul_le_mul_of_nonneg_right h8 hrest
        linarith [this]

/-- PROVED. The `4k²`-th root that turns the bound before (8) into display (8), p. 247, with
`C0 = 8` in place of the paper's slip `2^{8k²}` missing from `B`. -/
theorem karW_root {X B m P s : ℝ} {k : ℕ} (hk : 1 ≤ k) (hX : 0 ≤ X) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hP : 0 < P)
    (h : X ^ (4 * k ^ 2) ≤ (8 : ℝ) ^ (4 * k ^ 2) * B * m ^ (8 * k ^ 2) * P ^ (-(s / 2))) :
    X ≤ 8 * B ^ (1 / (4 * (k : ℝ) ^ 2)) * m ^ 2 * P ^ (-(s / (8 * (k : ℝ) ^ 2))) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2pos : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by positivity
  have hcast : ((4 * k ^ 2 : ℕ) : ℝ) = 4 * (k : ℝ) ^ 2 := by push_cast; ring
  have hb : (B ^ (1 / (4 * (k : ℝ) ^ 2))) ^ (4 * k ^ 2) = B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB, hcast, one_div_mul_cancel hk2pos.ne',
      Real.rpow_one]
  have hp : (P ^ (-(s / (8 * (k : ℝ) ^ 2)))) ^ (4 * k ^ 2) = P ^ (-(s / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le, hcast]
    congr 1
    field_simp
    ring
  have hmm : (m ^ 2) ^ (4 * k ^ 2) = m ^ (8 * k ^ 2) := by
    rw [← pow_mul]; congr 1; ring
  have hY0 : 0 ≤ 8 * B ^ (1 / (4 * (k : ℝ) ^ 2)) * m ^ 2 * P ^ (-(s / (8 * (k : ℝ) ^ 2))) := by
    have := Real.rpow_nonneg hB (1 / (4 * (k : ℝ) ^ 2))
    have := Real.rpow_nonneg hP.le (-(s / (8 * (k : ℝ) ^ 2)))
    positivity
  refine le_of_pow_le_pow_left₀ (n := 4 * k ^ 2) (by positivity) hY0 ?_
  rw [mul_pow, mul_pow, mul_pow, hb, hp, hmm]
  exact h

/-! ### The assembly, display (8) -/

/-- PROVED CONDITIONAL ON KarLemma1, a hypothesis of the statement. The
split of `leaf_karW_display8`, its exact type: display (8), Karacuba p. 247, with `C0 = 8`,
from (6), the bound of `𝔖` after (7) and Lemma 1, with `P2 + 1 ≤ 2 P^{e}`,
`e = c1/2 - 1/(2n²(n+1)) ≤ 1/2`, `n(n+1)(1-1/n)^l ≤ ρ(s_1 + ... + s_r)` and the
`4k²`-th root. -/
theorem leaf_karW_display8_split (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ C0 cc0 : ℝ, 0 < C0 ∧ 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a l : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P → 1 ≤ l →
          ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ l
            ≤ min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)) →
          min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ))
            < ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ (l - 1) →
          ‖∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
            eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
          ≤ C0 *
            ((30 * (((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ)) ^ 2) ^ n *
              (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
              (Real.log (P : ℝ)) ^ n) ^
              (1 / (4 * (((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ)) ^ 2)) *
            ((karP2 c1 n P : ℝ) + 1) ^ 2 *
            (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)) /
              (8 * (((n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ)) ^ 2))) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  obtain ⟨cc0, hcc0, h7⟩ := karW_display7 h3 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11
    hc241
  refine ⟨8, cc0, by norm_num, hcc0, ?_⟩
  intro N P n f T a l hP hn hn0 hbig hH ha haP hl hlo _hhi
  have hn12r : (12 : ℝ) ≤ n := le_trans (le_max_left _ _) hn0
  have hn12 : 12 ≤ n := by exact_mod_cast hn12r
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨k, hk⟩ : ∃ k, k = n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ := ⟨_, rfl⟩
  rw [← hk]
  have hk1 : 1 ≤ k := by
    have : 1 ≤ n * l := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hA4k : n * (n + 1) ≤ 4 * k := by
    have h0 := Nat.lt_floor_add_one (((n * (n + 1) : ℕ) : ℝ) / 4 + 1)
    have h2 : ((n * (n + 1) : ℕ) : ℝ) < 4 * (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℝ) := by
      linarith
    have h3' : n * (n + 1) < 4 * ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ := by exact_mod_cast h2
    omega
  have hAk2 : n * (n + 1) ≤ 4 * k ^ 2 := by nlinarith
  have hPr1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hlogP : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg hPr1
  have hmpos : (0 : ℝ) < (karP2 c1 n P : ℝ) + 1 := by positivity
  -- the three inputs
  have h56 := karW_display5_6 n (karP2 c1 n P) k hk1 (f (a : ℝ))
    (fun j => iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ))
  have hJ := karJ0_lemma1 h1 n l (karP2 c1 n P) hn12 hl
  rw [← hk] at hJ
  have hk7 : 7 ≤ k := by
    have : 12 ≤ n * l := le_trans hn12 (Nat.le_mul_of_pos_right n hl)
    omega
  have hS := h7 N P n f T a k hP hn hn0 hbig hH ha (by omega) hk7
  -- the size of P2 + 1
  have hscale : 1 ≤ c1 * (n : ℝ) ^ 2 :=
    LeanLab.ExceptionalSet.Decomp538a.karacuba_large_order_scale c1 n hc1
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn0)
  have hfl := LeanLab.ExceptionalSet.Decomp538a.karacuba_shift_floor_bounds c1 n P hc1 hn hP hscale
  have hM1 : 1 ≤ karP2 c1 n P := hfl.1
  have hMe : (karP2 c1 n P : ℝ) ≤ (P : ℝ) ^ (c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))) := by
    rw [karP2]
    exact Nat.floor_le (Real.rpow_nonneg hPpos.le _)
  have hm2 : (karP2 c1 n P : ℝ) + 1 ≤
      2 * (P : ℝ) ^ (c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))) := by
    have : (1 : ℝ) ≤ karP2 c1 n P := by exact_mod_cast hM1
    linarith
  have he2 : c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) ≤ 1 / 2 := by
    have : 0 ≤ 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) := by positivity
    linarith
  have hq0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; linarith
    linarith
  have hq1 : 1 - 1 / (n : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hql : (1 - 1 / (n : ℝ)) ^ l ≤ 1 := pow_le_one₀ hq0 hq1
  have hql0 : 0 ≤ (1 - 1 / (n : ℝ)) ^ l := pow_nonneg hq0 l
  have hAr0 : (0 : ℝ) ≤ ((n * (n + 1) : ℕ) : ℝ) := by positivity
  have hx0 : 0 ≤ ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ l := by positivity
  have hxA : ((n * (n + 1) : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) ^ l ≤ ((n * (n + 1) : ℕ) : ℝ) := by
    nlinarith
  have hmx := karW_m_pow_x hmpos.le hPr1 hm2 he2 hx0 hxA hlo
  have hpow := karW_pow_m ((karP2 c1 n P : ℝ) + 1) (1 - 1 / (n : ℝ)) hmpos k (n * (n + 1)) l hk1
  have hJ' : karJ0 n k (karP2 c1 n P) ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
      ((karP2 c1 n P : ℝ) + 1) ^ (2 * (k : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
        + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := hJ.le
  have hS' : ∏ s ∈ Finset.Icc 1 n,
      karSigma k (karP2 c1 n P) s (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ)) ≤
      (4 : ℝ) ^ (n * (n + 1)) *
        ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (Real.log (P : ℝ)) ^ n) *
        ((karP2 c1 n P : ℝ) + 1) ^ (n * (n + 1)) *
        (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)))) :=
    le_of_le_of_eq hS (by ring)
  have hX4 := karW_combine hmpos hPpos (karJ0_nonneg _ _ _)
    (Finset.prod_nonneg fun s _ => karSigma_nonneg _ _ _ _) (by positivity)
    (Real.rpow_nonneg (by positivity) _) hAk2 h56 hJ' hS' hpow hmx
  rw [karW_D_sq] at hX4
  have hX4' : _ ≤ (8 : ℝ) ^ (4 * k ^ 2) *
      ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
        (Real.log (P : ℝ)) ^ n) * ((karP2 c1 n P : ℝ) + 1) ^ (8 * k ^ 2) *
      (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)) / 2)) :=
    le_of_le_of_eq hX4 (by ring)
  exact karW_root hk1 (norm_nonneg _) (by positivity) hmpos.le hPpos hX4'

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
