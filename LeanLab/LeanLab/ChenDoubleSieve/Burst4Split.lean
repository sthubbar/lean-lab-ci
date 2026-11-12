import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Discretization
import LeanLab.ChenDoubleSieve.TableInputsBridge

/-!
# Burst 4 split of Wu 2004 Theorem 1, `D(N) ≤ 7.8209 Θ(N)`

P0036 J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
Acta Arith. 114 (2004) 215 to 273, arXiv 0705.1652, Theorem 1, proved in Section 7,
pages 30 and 31 of the arXiv version.

AI wrote this Lean code. Binary Goldbach is OPEN; this is an upper bound for `D(N)`.

The paper's proof of Theorem 1 has this top level structure.
* Section 3, pages 9 and 10: the correction functions `H` and `h`, here represented by
  real functions, `corrections_real`.
* Proposition 1, page 10: `H ≥ 0`, `proposition1`.
* Corollary 1, page 13: `H` is decreasing on `[1, 10]`, `corollary1`.
* Propositions 3 and 4, pages 14 and 15, displays 3.21 and 3.22: `proposition3`, `proposition4`.
* Table 1, page 30: the four `Ψ₂` lower bounds, `table1_Psi2`; the five `Ψ₁` bounds are
  already PROVED in the folder, `Wu04PrintedPsi1.table1_Psi1_bounds`.
* Displays 7.1 and 7.2, page 30: the entries `a_{i,j}`; their existence, `table_kernel_integrable`,
  and their numerical lower bounds, `integral_matrix_bound`.
* Displays 7.3 and 7.4, pages 30 and 31: `H(2.2) ≥ 0.0223938`, already PROVED in the folder from
  the above as `Wu04Discretization.correction_of_functional`.
* Page 31, last display: Lemma 3.2 with `σ = {1}`, `s = 2.2`, `theorem1_final_display`.

`wu2004_thm1_of_split` proves the exact statement of `wu2004_thm1` from these leaves with no
sorry of its own.
-/

noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst4Split
open Wu04Functional

/-! ### The sorry leaves, each a cited step of Wu's proof -/

/-- LEAF. Wu 2004 Section 3, pages 9 and 10, the definitions of `H_{k,N₀}`, `H_k`, `H`, and the
same for `h`, with Lemma 3.2 and Proposition 1. For `δ` sufficiently small, as fixed at the start
of Section 3, the extended real corrections are finite on `[1, 10]` and so are represented by
real functions. Finiteness: `Φ ≥ 0` bounds `H` above by `A(s)`, and Proposition 1 bounds it below
by `0`; similarly for `h`. -/
theorem corrections_real {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ H h : ℝ → ℝ, RepresentsCorrections F f δ H h := by
  sorry

/-- LEAF. Wu 2004 Proposition 1, page 10: `H_k(s) ≥ 0` and `h_k(s) ≥ 0` for `s ∈ [1, 10]`,
hence `H(s) ≥ 0` and `h(s) ≥ 0`. Its proof applies Lemma 2.2, the linear sieve, and Lemma 2.3,
the Bombieri Vinogradov type mean value theorem, both cited by Wu. -/
theorem proposition1 {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ s ∈ Icc (1 : ℝ) 10, 0 ≤ H s ∧ 0 ≤ h s := by
  sorry

/-- LEAF. Wu 2004 Corollary 1, page 13: `H(s)` is decreasing on `[1, 10]`. Wu proves it from
`A(s) = 1` on `[1, 3]` and from Propositions 1 and 2 on `[3, 10]`. -/
theorem corollary1 {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → AntitoneOn H (Icc (1 : ℝ) 10) := by
  sorry

/-- LEAF. Wu 2004 Proposition 3, page 14, display 3.21, proved in Section 6, page 29, from
Lemma 4.1 and Lemma 5.1: `H(s) ≥ Ψ₁(s) + ∫₁³ H(t) Ξ₁(t; s) dt` for `5 ≥ s' ≥ 3 ≥ s ≥ 2` and
`s' − s'/s ≥ 2`. -/
theorem proposition3 {F f ω : ℝ → ℝ} (hF : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → Proposition3 H ω := by
  sorry

/-- LEAF. Wu 2004 Proposition 4, page 15, display 3.22, proved in Section 6, page 29, from
Lemma 4.2 and Lemma 5.2: `H(s) ≥ Ψ₂(s) + ∫₁³ H(t) Ξ₂(t; s) dt` on the parameter range stated
there. -/
theorem proposition4 {F f ω : ℝ → ℝ} (hF : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → Proposition4 H ω := by
  sorry

/-- LEAF. Wu 2004 Table 1, page 30, column `Ψ₂(sᵢ)`, rows 1 to 4: the printed values
`0.015826357, 0.015247971, 0.013898757, 0.011776059` are lower bounds for `Ψ₂` at the printed
parameters. The `Ψ₁` column, rows 5 to 9, is already PROVED as
`Wu04PrintedPsi1.table1_Psi1_bounds`. -/
theorem table1_Psi2 {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∀ i : Fin 4, tablePsi ⟨i.val, by omega⟩ ≤ Psi2 ω (tableParams i) := by
  sorry

/-- LEAF. Wu 2004 displays 7.1 and 7.2, page 30: the entries `a_{i,j} = ∫_{s_{j−1}}^{s_j} Ξ(t, sᵢ) dt`
are finite integrals, that is, each of the nine kernels `Ξ₂(·; sᵢ)`, `i ≤ 4`, and `Ξ₁(·; sᵢ)`,
`i ≥ 5`, is integrable on `[1, 3]`. -/
theorem table_kernel_integrable :
    ∀ i : Fin 9, IntervalIntegrable (Wu04Table.tableKernel i) volume 1 3 := by
  sorry

/-- LEAF. Wu 2004 displays 7.1 and 7.2, page 30, the matrix `A` of page 31 computed by Wu with
Maple: the rational candidate entries of `Wu04Table.candidateMatrixQ` are lower bounds for the
actual integrals `a_{i,j}`. With these bounds the folder's exact dual certificate replaces Wu's
statement that `(I − A)⁻¹` has positive entries. -/
theorem integral_matrix_bound : Wu04Table.IntegralMatrixBound := by
  sorry

/-- LEAF. Wu 2004 page 31, the last display of Section 7: taking `σ = {1}` and `s = 2.2` in
display 3.3 of Lemma 3.2,
`D(N) ≤ S(A; P(N), N^{(1/2−δ)/2.2}) = Φ(N, {1}, 2.2) ≤ {A(2.2) − H_{k,N₀}(2.2)} 4 C_N li(N)/log N^{1/2−δ}`,
with `A(2.2) = 1` and `li(N) ∼ N / log N`. Here every `c < H(2.2)` is below `H_{1,N₀}(2.2)` for
large `N₀`, and the factor `1 + ε` absorbs `li(N) ∼ N/log N` and the primes `N − p` below the
sifting level. -/
theorem theorem1_final_display {F f : ℝ → ℝ} (hF : IsLinearSieve F f)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {H h : ℝ → ℝ}
    (hR : RepresentsCorrections F f δ H h) {c : ℝ} (hc : c < H 2.2) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N →
      (D N : ℝ) ≤ (1 + ε) * (8 * (1 - c) / (1 - 2 * δ)) * Θ N := by
  sorry

/-! ### Proved glue -/

/-- The products `H(t) Ξ(t; sᵢ)` in displays 7.1 and 7.2 are integrable when `H` is decreasing
and the kernel is integrable, since a monotone function is bounded and measurable on `[1, 3]`. -/
theorem product_integrable {H K : ℝ → ℝ} (hH : AntitoneOn H (Icc (1 : ℝ) 3))
    (hK : IntervalIntegrable K volume 1 3) :
    IntervalIntegrable (fun t => H t * K t) volume 1 3 := by
  have h13 : (1 : ℝ) ≤ 3 := by norm_num
  have hH' : AntitoneOn H (uIcc (1 : ℝ) 3) := by rwa [uIcc_of_le h13]
  have hHi : IntervalIntegrable H volume 1 3 := hH'.intervalIntegrable
  rw [intervalIntegrable_iff] at hHi hK ⊢
  refine Integrable.bdd_mul (c := |H 1| + |H 3|) hK hHi.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
  rw [uIoc_of_le h13] at ht
  have ht' : t ∈ Icc (1 : ℝ) 3 := ⟨ht.1.le, ht.2⟩
  have hup : H t ≤ H 1 := hH ⟨le_rfl, h13⟩ ht' ht'.1
  have hlo : H 3 ≤ H t := hH ht' ⟨h13, le_rfl⟩ ht'.2
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (H 3), abs_nonneg (H 1)]
  · linarith [le_abs_self (H 1), abs_nonneg (H 3)]

/-- The final constant: with `δ ≤ 10⁻⁷`, `ε = 10⁻⁶` and `c = 0.0223937`, the factor is at most
`7.8209`. This uses the slack between `8 (1 − 0.0223938) = 7.82085…` and `7.8209` on page 31. -/
theorem final_constant {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 10000000) :
    (1 + 1 / 1000000) * (8 * (1 - 223937 / 10000000) / (1 - 2 * δ)) ≤ (7.8209 : ℝ) := by
  have hpos : 0 < 1 - 2 * δ := by linarith
  rw [← mul_div_assoc, div_le_iff₀ hpos]
  norm_num
  linarith

/-- **Wu 2004 Theorem 1 from the split.** The exact statement of `wu2004_thm1`, proved from the
leaves above and the PROVED folder lemmas `Task275.standard_functions`,
`Wu04Table.tableKernel_nonnegative`, `Wu04Table.functional_rows`, which uses the PROVED
`Wu04PrintedPsi1.table1_Psi1_bounds`, and `Wu04Discretization.correction_of_functional`.
CONDITIONAL ON the nine sorry leaves. -/
theorem wu2004_thm1_of_split : GoldbachUpper 7.8209 := by
  obtain ⟨F, f, ω, hF, hω⟩ := Task275.standard_functions
  obtain ⟨d1, hd1, hC⟩ := corrections_real hF
  obtain ⟨d2, hd2, h1⟩ := proposition1 hF
  obtain ⟨d3, hd3, hA⟩ := corollary1 hF
  obtain ⟨d4, hd4, h3⟩ := proposition3 hF hω
  obtain ⟨d5, hd5, h4⟩ := proposition4 hF hω
  set m := min d1 (min d2 (min d3 (min d4 d5))) with hm
  have hm0 : 0 < m := by
    simp only [hm, lt_min_iff]
    exact ⟨hd1, hd2, hd3, hd4, hd5⟩
  set δ := min (m / 2) (1 / 10000000) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδm : δ < m := (min_le_left _ _).trans_lt (by linarith)
  have hδs : δ ≤ 1 / 10000000 := min_le_right _ _
  have hm1 : m ≤ d1 := min_le_left _ _
  have hm2 : m ≤ d2 := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : m ≤ d3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm4 : m ≤ d4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hm5 : m ≤ d5 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨H, h, hR⟩ := hC δ hδ0 (hδm.trans_le hm1)
  have hnn := h1 δ hδ0 (hδm.trans_le hm2) H h hR
  have hanti := hA δ hδ0 (hδm.trans_le hm3) H h hR
  have hp3 := h3 δ hδ0 (hδm.trans_le hm4) H h hR
  have hp4 := h4 δ hδ0 (hδm.trans_le hm5) H h hR
  have hdec : AntitoneOn H (Icc (1 : ℝ) 3) :=
    hanti.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hT : Wu04Discretization.TableInputs H :=
    { nonnegative := fun t ht => (hnn t ⟨ht.1, by linarith [ht.2]⟩).1
      decreasing := hdec
      kernel_nonnegative := fun i t ht => Wu04Table.tableKernel_nonnegative i ht
      kernel_integrable := table_kernel_integrable
      product_integrable := fun i => product_integrable hdec (table_kernel_integrable i)
      functional := Wu04Table.functional_rows hω hp3 hp4 (table1_Psi2 hω) }
  have hx : (223938 / 10000000 : ℝ) ≤ H (2.2 : ℝ) :=
    Wu04Discretization.correction_of_functional H hT integral_matrix_bound
  have hc : (223937 / 10000000 : ℝ) < H 2.2 := by linarith
  obtain ⟨N₀, hN₀⟩ := theorem1_final_display hF hδ0 (by linarith) hR hc
    (ε := 1 / 1000000) (by norm_num)
  refine ⟨N₀, fun N hE hN => (hN₀ N hE hN).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (final_constant hδ0 hδs) (Θ_nonneg N)

end LeanLab.ChenDoubleSieve.Burst4Split
