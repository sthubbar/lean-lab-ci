import LeanLab.MissingDigit.Statements

/-!
# Burst 4 split of Kim, Theorem 1.1

Paper: P0057, J. Kim, "Goldbach's problem in short intervals for numbers with a missing digit",
arXiv 2412.19975v1, Section 2 "Proof of Theorem 1.1", pages 7 to 11.

AI wrote this Lean code. Binary Goldbach is OPEN.

The cited main result `LeanLab.MissingDigit.kim_thm1_1 : D4Bound (3 / 5) 7` carries an open step
in `Statements.lean`, which is left untouched. Here `kim_thm1_1_of_split` proves the same
statement from the top level structure of the paper's Section 2 proof:

* `orthogonality`, the circle method identity behind the left side of display (2.1),
  page 8. PROVED.
* `arc_split`, the translation of `[0,1]` to `[1/Q, 1+1/Q]` and its splitting into the major
  arcs `𝔐` and minor arcs `𝔪` of page 3. PROVED.
* `prop_2_2`, Proposition 2.2, page 8, resting on Proposition 2.1 = MSTT Theorem 1.1 (iii)
  and Lemma 1.7, cited and open.
* `major_arcs_bound`, Proposition 2.4, page 9, together with Section 2.2, pages 10 and 11.
  cited and open.
* `prop_2_5`, Proposition 2.5, page 9, resting on Proposition 3.4, cited and open.

Notation follows Section 1.1 and Section 2 of the paper with `X = g^k`:
`R₄ = X^{ε/40}`, `δ = X^{-ε}`, `Q = δ^{-1} = X^ε`, `D(δ) = (log X)^{-3^6-1}`,
`β(δ) = 1 / (H δ D(δ))`.
-/

namespace LeanLab.MissingDigit.Burst4Split

open Finset Real MeasureTheory
open LeanLab.MissingDigit

attribute [local instance] Classical.propDecidable

/-! ### Definitions from the paper -/

/-- `e(α) = e^{2πiα}`, page 2. -/
noncomputable def eC (α : ℝ) : ℂ := Complex.exp (2 * (π : ℂ) * Complex.I * (α : ℂ))

/-- The paper's polynomial `P_m(t)`, page 7, with parameter `R = R₄`:
`P_m(t) = ∑_{j=0}^{3} C(4,j) ∑_{m = n₁ n₂ n₃, n₁,…,n_j ≤ R, R < n_{j+1},…,n₃ ≤ R²}
  (t - log(n₁ ⋯ n_j R^{4-j}))^{4-j-1} / ((4-j-1)! log^{4-j-1} R)`.
The `n_i` are positive integers. -/
noncomputable def Pm (R : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ range 4, (Nat.choose 4 j : ℝ) *
    ∑ v ∈ (Fintype.piFinset fun _ : Fin 3 => Icc 1 ⌊R ^ 2⌋₊).filter
        (fun v => v 0 * v 1 * v 2 = m ∧ (∀ i : Fin 3, i.val < j → (v i : ℝ) ≤ R) ∧
          (∀ i : Fin 3, j ≤ i.val → R < (v i : ℝ) ∧ (v i : ℝ) ≤ R ^ 2)),
      (t - Real.log ((∏ i ∈ (univ : Finset (Fin 3)).filter (fun i => i.val < j), (v i : ℝ)) *
          R ^ (4 - j))) ^ (3 - j) /
        ((Nat.factorial (3 - j) : ℝ) * Real.log R ^ (3 - j))

/-- `R₄ = X^{ε/40}`, page 7. -/
noncomputable def R4 (ε : ℝ) (X : ℕ) : ℝ := (X : ℝ) ^ (ε / 40)

/-- The MSTT approximant `d♯₄(n) = ∑_{m ≤ R₄⁶, m ∣ n} P_m(log n)`, page 7. -/
noncomputable def d4sharp (ε : ℝ) (X n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m : ℕ => ((m : ℕ) : ℝ) ≤ R4 ε X ^ 6),
    Pm (R4 ε X) (m : ℕ) (Real.log n)

/-- `S₄(α; H) = ∑_{X ≤ n ≤ X+H} d₄(n) e(nα)`, page 7. -/
noncomputable def S4 (X : ℕ) (H : ℝ) (α : ℝ) : ℂ :=
  ∑ n ∈ Icc X (X + ⌊H⌋₊), (dk 4 n : ℂ) * eC (n * α)

/-- `S♯₄(α; H) = ∑_{X ≤ n ≤ X+H} d♯₄(n) e(nα)`, page 7. -/
noncomputable def S4sharp (ε : ℝ) (X : ℕ) (H : ℝ) (α : ℝ) : ℂ :=
  ∑ n ∈ Icc X (X + ⌊H⌋₊), (d4sharp ε X n : ℂ) * eC (n * α)

/-- `Q = δ^{-1}` with `δ = X^{-ε}`, page 2. -/
noncomputable def Qpar (ε : ℝ) (X : ℕ) : ℝ := (X : ℝ) ^ ε

/-- `δ = X^{-ε}`, page 2. -/
noncomputable def delta (ε : ℝ) (X : ℕ) : ℝ := (X : ℝ) ^ (-ε)

/-- `D(δ) = (log X)^{-3^6-1}`, page 3. -/
noncomputable def Ddelta (X : ℕ) : ℝ := (Real.log X ^ (3 ^ 6 + 1 : ℕ))⁻¹

/-- `β(δ) = 1 / (H δ D(δ))`, page 3. -/
noncomputable def betaDelta (ε : ℝ) (X : ℕ) (H : ℝ) : ℝ := 1 / (H * delta ε X * Ddelta X)

/-- The major arcs `𝔐 = ⋃_{q ≤ Q} ⋃_{1 ≤ r ≤ q, (r,q)=1} [r/q - β(δ), r/q + β(δ)]`, page 3. -/
noncomputable def majorArcs (ε : ℝ) (X : ℕ) (H : ℝ) : Set ℝ :=
  ⋃ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ⋃ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
    Set.Icc ((r : ℝ) / q - betaDelta ε X H) ((r : ℝ) / q + betaDelta ε X H)

/-- The range of integration `[1/Q, 1+1/Q]` of page 3, taken half open, which changes no
integral. -/
noncomputable def arcRange (ε : ℝ) (X : ℕ) : Set ℝ :=
  Set.Ioc (1 / Qpar ε X) (1 + 1 / Qpar ε X)

/-- The paper's `∫_{α ∈ 𝔐} S♯₄(α; H) e(-nα) dα`, page 9. -/
noncomputable def majorInt (ε : ℝ) (X : ℕ) (H : ℝ) (n : ℕ) : ℂ :=
  ∫ α in arcRange ε X ∩ majorArcs ε X H, S4sharp ε X H α * eC (-(n * α))

/-- The paper's `∫_{α ∈ 𝔪} S♯₄(α; H) e(-nα) dα` with `𝔪 = [1/Q, 1+1/Q] \ 𝔐`, page 9. -/
noncomputable def minorInt (ε : ℝ) (X : ℕ) (H : ℝ) (n : ℕ) : ℂ :=
  ∫ α in arcRange ε X \ majorArcs ε X H, S4sharp ε X H α * eC (-(n * α))

/-! ### Proved leaves -/

theorem eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem eC_int (m : ℤ) : eC m = 1 := by
  unfold eC
  have : 2 * (π : ℂ) * Complex.I * ((m : ℝ) : ℂ) = m * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem continuous_eC : Continuous eC := by
  unfold eC; fun_prop

/-- `∫_0^1 e(kα) dα = [k = 0]` for an integer `k`. -/
theorem integral_eC_int (k : ℤ) : ∫ α in (0 : ℝ)..1, eC (k * α) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]
  · have hc : (2 * (π : ℂ) * Complex.I * k) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have h1 : (fun α : ℝ => eC (k * α)) =
        fun α : ℝ => Complex.exp ((2 * (π : ℂ) * Complex.I * k) * α) := by
      funext α; unfold eC; congr 1; push_cast; ring
    rw [h1, integral_exp_mul_complex hc]
    have h2 : Complex.exp (2 * (π : ℂ) * Complex.I * k) = 1 := by
      have := eC_int k; unfold eC at this; rw [← this]; congr 1
    simp [h2]

/-- Leaf 1, PROVED. The circle method orthogonality behind the left side of display (2.1),
page 8: for `n` in the range of a finite exponential sum, `∫_0^1 (∑_m c_m e(mα)) e(-nα) dα = c_n`.
Specialised to `S₄(α; H)` this gives `∫_0^1 S₄(α;H) e(-nα) dα = d₄(n)` for `X ≤ n ≤ X+H`. -/
theorem orthogonality (s : Finset ℕ) (c : ℕ → ℂ) {n : ℕ} (hn : n ∈ s) :
    ∫ α in (0 : ℝ)..1, (∑ m ∈ s, c m * eC (m * α)) * eC (-(n * α)) = c n := by
  have hint : ∀ m : ℕ, IntervalIntegrable (fun α : ℝ => c m * eC (m * α) * eC (-(n * α)))
      volume 0 1 := fun m =>
    (by
      have : Continuous (fun α : ℝ => c m * eC (m * α) * eC (-(n * α))) := by
        have := continuous_eC
        fun_prop
      exact this.intervalIntegrable 0 1)
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun m _ => hint m)]
  have key : ∀ m : ℕ, (∫ α in (0 : ℝ)..1, c m * eC (m * α) * eC (-(n * α))) =
      if m = n then c m else 0 := by
    intro m
    have h1 : (fun α : ℝ => c m * eC (m * α) * eC (-(n * α))) =
        fun α : ℝ => c m * eC (((m : ℤ) - n : ℤ) * α) := by
      funext α; rw [mul_assoc, ← eC_add]; congr 2; push_cast; ring
    rw [h1, intervalIntegral.integral_const_mul, integral_eC_int]
    by_cases h : m = n
    · subst h; simp
    · have : ((m : ℤ) - n) ≠ 0 := by omega
      simp [h, this]
  simp_rw [key]
  rw [Finset.sum_ite_eq' s n c]; simp [hn]

theorem measurableSet_majorArcs (ε : ℝ) (X : ℕ) (H : ℝ) :
    MeasurableSet (majorArcs ε X H) := by
  unfold majorArcs
  refine Finset.measurableSet_biUnion _ fun q _ => ?_
  exact Finset.measurableSet_biUnion _ fun r _ => measurableSet_Icc

/-- Leaf 2, PROVED. The arc decomposition of page 3 used in Section 2: for a continuous
`1`-periodic integrand, `∫_0^1 = ∫_{𝔐} + ∫_{𝔪}` with `𝔐 ∪ 𝔪 = [1/Q, 1+1/Q]`. -/
theorem arc_split (ε : ℝ) (X : ℕ) (H : ℝ) (F : ℝ → ℂ) (hF : Continuous F)
    (hper : Function.Periodic F 1) :
    ∫ α in (0 : ℝ)..1, F α =
      (∫ α in arcRange ε X ∩ majorArcs ε X H, F α) +
        ∫ α in arcRange ε X \ majorArcs ε X H, F α := by
  unfold arcRange
  rw [integral_inter_add_sdiff (measurableSet_majorArcs ε X H)
    ((hF.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)]
  have h := hper.intervalIntegral_add_eq 0 (1 / Qpar ε X)
  rw [zero_add] at h
  rw [h, intervalIntegral.integral_of_le (by linarith : 1 / Qpar ε X ≤ 1 / Qpar ε X + 1)]
  rw [add_comm (1 / Qpar ε X) 1]

/-! ### Cited leaves, the paper's Propositions -/

/-- LEAF: Kim, Proposition 2.2, display (2.1), page 8: for
`X^{3/5+ε} ≤ H ≤ X^{1-ε}` and `g` sufficiently large,
`∑_{n ∈ [X,X+H]^*} ∫_{[0,1]} S₄(α;H) e(-nα) dα = ∑_{n ∈ [X,X+H]^*} ∫_{[0,1]} S♯₄(α;H) e(-nα) dα
+ o(|[X,X+H]^*|)`. Its proof uses Proposition 2.1, which is MSTT Theorem 1.1 (iii), and the
`L¹` bound of Lemma 1.7. Here `o(|[X,X+H]^*|)` is encoded as: for every `η > 0` the difference
is at most `η |[X,X+H]^*|` once `k` is large; `ε` is small, as the paper assumes in Section 1.1. -/
theorem prop_2_2 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H,
          ∫ α in (0 : ℝ)..1, (S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) * eC (-(n * α))‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  sorry

/-- LEAF: Kim, Proposition 2.4, display (2.6), page 9, combined with the
evaluation of its main term in Section 2.2, displays (2.8) to (2.11), pages 10 and 11: the major
arc contribution satisfies
`∑_{n ∈ [X,X+H]^*} ∫_{𝔐} S♯₄(α;H) e(-nα) dα ≪ (log X)^7 |[X,X+H]^*|`
for `X^{3/5+ε} ≤ H ≤ X^{1-ε}` and `g` sufficiently large. The seven logarithms are
`(log X)^2` from (2.10), `(log X)^2` from (2.11), which uses Lemma 2.6 of Dartyge and Mauduit,
and `(log X)^3` from the sum over `m` of `d₃(m)/m`. -/
theorem major_arcs_bound : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card := by
  sorry

/-- LEAF: Kim, Proposition 2.5, page 9: the minor arc contribution is
`∑_{n ∈ [X,X+H]^*} ∫_{𝔪} S♯₄(α;H) e(-nα) dα = o(|[X,X+H]^*|)`, from the supremum bound of
Proposition 3.4 and Proposition 3.5 together with Lemma 1.7. The paper prints `o(|[1.H]^*|)`,
an evident misprint for `o(|[X,X+H]^*|)`, which is what the proof gives and what Section 2.2
uses. Encoded as in `prop_2_2`. -/
theorem prop_2_5 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, minorInt ε (g ^ k) H n‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  sorry

/-! ### Assembly -/

theorem S4sharp_continuous (ε : ℝ) (X : ℕ) (H : ℝ) (n : ℕ) :
    Continuous (fun α => S4sharp ε X H α * eC (-(n * α))) := by
  unfold S4sharp
  have := continuous_eC
  fun_prop

theorem S4sharp_periodic (ε : ℝ) (X : ℕ) (H : ℝ) (n : ℕ) :
    Function.Periodic (fun α => S4sharp ε X H α * eC (-(n * α))) 1 := by
  intro α
  have hm : ∀ m : ℕ, eC (m * (α + 1)) = eC (m * α) := by
    intro m
    rw [mul_add, mul_one, eC_add]
    have := eC_int m; push_cast at this; rw [this, mul_one]
  have hn : eC (-(n * (α + 1))) = eC (-(n * α)) := by
    rw [mul_add, mul_one, neg_add, eC_add]
    have := eC_int (-(n : ℤ)); push_cast at this; rw [this, mul_one]
  simp only [S4sharp, hm, hn]

/-- The identity of Section 2: `∑_{n ∈ [X,X+H]^*} d₄(n)` equals the Proposition 2.2 difference
plus the major and minor arc contributions. -/
theorem sum_decomp (ε : ℝ) (X : ℕ) (g b : ℕ) (H : ℝ) :
    ((∑ n ∈ starSet g b X H, (dk 4 n : ℝ) : ℝ) : ℂ) =
      (∑ n ∈ starSet g b X H,
          ∫ α in (0 : ℝ)..1, (S4 X H α - S4sharp ε X H α) * eC (-(n * α))) +
        (∑ n ∈ starSet g b X H, majorInt ε X H n) +
        ∑ n ∈ starSet g b X H, minorInt ε X H n := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnI : n ∈ Icc X (X + ⌊H⌋₊) := by
    unfold starSet at hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]; omega
  have hS4 := orthogonality (Icc X (X + ⌊H⌋₊)) (fun m => (dk 4 m : ℂ)) hnI
  have hsplit := arc_split ε X H _ (S4sharp_continuous ε X H n) (S4sharp_periodic ε X H n)
  have hci : ∀ f : ℝ → ℂ, Continuous f → IntervalIntegrable f volume 0 1 :=
    fun f hf => hf.intervalIntegrable 0 1
  have hS4c : Continuous (fun α => S4 X H α * eC (-(n * α))) := by
    unfold S4; have := continuous_eC; fun_prop
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (hci _ hS4c) (hci _ (S4sharp_continuous ε X H n))]
  unfold majorInt minorInt
  rw [hsplit]
  unfold S4
  rw [hS4]
  ring

/-- Kim, Theorem 1.1, assembled from the paper's Section 2 structure. Same statement as
`LeanLab.MissingDigit.kim_thm1_1`. -/
theorem kim_thm1_1_of_split : D4Bound (3 / 5) 7 := by
  obtain ⟨e1, he1, h1⟩ := prop_2_2
  obtain ⟨e2, he2, h2⟩ := major_arcs_bound
  obtain ⟨e3, he3, h3⟩ := prop_2_5
  intro ε hε
  set ε' : ℝ := min ε (min e1 (min e2 e3)) / 2 with hε'
  have hmin_pos : 0 < min ε (min e1 (min e2 e3)) := lt_min hε (lt_min he1 (lt_min he2 he3))
  have hε'pos : 0 < ε' := by positivity
  have hε'lt : ε' < min ε (min e1 (min e2 e3)) := by rw [hε']; linarith
  have hε'1 : ε' < e1 := lt_of_lt_of_le hε'lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'2 : ε' < e2 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε'3 : ε' < e3 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε'ε : ε' < ε := lt_of_lt_of_le hε'lt (min_le_left _ _)
  obtain ⟨g1, hg1⟩ := h1 ε' hε'pos hε'1
  obtain ⟨g2, hg2⟩ := h2 ε' hε'pos hε'2
  obtain ⟨g3, hg3⟩ := h3 ε' hε'pos hε'3
  refine ⟨max g1 (max g2 g3), fun g b hg hb2 hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_max_left _ _) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hg
  have hgg3 : g3 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hg
  have hg2' : 2 ≤ g := by omega
  obtain ⟨K1, hK1⟩ := hg1 g b hgg1 hb2 hbg 1 one_pos
  obtain ⟨C, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := hg3 g b hgg3 hb2 hbg 1 one_pos
  -- `X = g^k` tends to infinity, so eventually `X^{ε-ε'} ≥ max (1/A₁) A₂` and `X ≥ 3`.
  have hX : Filter.Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun k : ℕ => (g : ℝ) ^ k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
    simpa using this
  have hXc := (tendsto_rpow_atTop (by linarith : 0 < ε - ε')).comp hX
  obtain ⟨K4, hK4⟩ := Filter.eventually_atTop.1
    (hXc.eventually_ge_atTop (max (1 / A₁) A₂))
  obtain ⟨K5, hK5⟩ := Filter.eventually_atTop.1 (hX.eventually_ge_atTop 3)
  refine ⟨max C 0 + 2, max K1 (max K2 (max K3 (max K4 K5))), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  have hk4 : K4 ≤ k := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  have hk5 : K5 ≤ k := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hX3 : (3 : ℝ) ≤ X := hK5 k hk5
  have hXpos : 0 < X := by linarith
  have hXpow : max (1 / A₁) A₂ ≤ X ^ (ε - ε') := hK4 k hk4
  have hA1 : 1 / A₁ ≤ X ^ (ε - ε') := le_trans (le_max_left _ _) hXpow
  have hA2 : A₂ ≤ X ^ (ε - ε') := le_trans (le_max_right _ _) hXpow
  -- the hypotheses of the leaves at `ε'`
  have hlo' : X ^ ((3 : ℝ) / 5 + ε') ≤ H := by
    refine le_trans ?_ hlo
    have hsplit : X ^ ((3 : ℝ) / 5 + ε) = X ^ ((3 : ℝ) / 5 + ε') * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have h1 : 1 ≤ A₁ * X ^ (ε - ε') := by
      have := mul_le_mul_of_nonneg_left hA1 hA₁.le
      rwa [mul_one_div_cancel hA₁.ne'] at this
    have hp : 0 ≤ X ^ ((3 : ℝ) / 5 + ε') := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have hhi' : H ≤ X ^ (1 - ε') := by
    refine le_trans hhi ?_
    have hsplit : X ^ (1 - ε') = X ^ (1 - ε) * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ X ^ (1 - ε) := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have b1 := hK1 k H hk1 hlo' hhi'
  have b2 := hK2 k H hk2 hlo' hhi'
  have b3 := hK3 k H hk3 hlo' hhi'
  have hdec := sum_decomp ε' (g ^ k) g b H
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have hS : (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
      1 * N + C * Real.log X ^ 7 * N + 1 * N := by
    have hnn : 0 ≤ ∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
        = ‖((∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ _ := by
          rw [hdec]
          refine le_trans (norm_add₃_le) ?_
          linarith
  have hC : C * Real.log X ^ 7 * N ≤ max C 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C 0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
      ≤ 1 * N + C * Real.log X ^ 7 * N + 1 * N := hS
    _ ≤ (max C 0 + 2) * Real.log X ^ 7 * N := by nlinarith

#check (kim_thm1_1_of_split : D4Bound (3 / 5) 7)
#check (kim_thm1_1 : D4Bound (3 / 5) 7)

end LeanLab.MissingDigit.Burst4Split
