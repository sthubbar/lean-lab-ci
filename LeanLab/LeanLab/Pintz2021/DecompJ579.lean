import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.DecompJ281

namespace LeanLab.Pintz2021.DecompJ579

open Complex Finset Filter Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53
open LeanLab.Pintz2021.DecompJ281

attribute [local instance] Classical.propDecidable

noncomputable section

/-
RETIRED 2026-10-31 architect PC 20261031T2333Z-383, kept as text. Two leaves of the task579 split:
`leaf_constants_exist : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∃ c H0 X0 : ℝ, 0 < c`
and `leaf_main_term_bound_exists_C (ε ε0 c H0 X0 : ℝ) : ∃ C : ℝ, ∀ H X P0 P Sg', Thm1Hyp_v2 ε H0 X0 H X P0 →
P0 * X ^ (-ε) ≤ P → P ≤ P0 → (convergence of every pair series at every m : ℕ) → ∀ m : ℕ, m ≤ X →
‖R1majPrime ε X P m - mainTermPrime E Sg' ε X m‖ ≤ C * (Sing m * X * exp (-(c * H)) + X ^ (1 - ε0))`.
The second was vacuous: its convergence hypothesis includes m = 0, where the pole series diverges,
Audit168.zero_no_limit and LeafAudit168.prime_zero_no_limit; and once m = 0 is dropped it would be
asked for every ε0 and c, which the paper never claims. The first carried no content. They are
merged below into `leaf_main_term_bound`, with ε0 and c existential as in Theorem 1.
-/

/-! ### The level `P` of display 8.28 and finiteness of the exceptional set

`leaf_P_exists` is proved here, not cited: the level `P = P0` lies in the interval
`[P0 X^{-ε}, P0]` because `Thm1Hyp` gives `1 ≤ P0 ≤ X^{4/9-ε}` with `0 < ε < 4/9`, hence
`|X| ≥ 1` and `X^{-ε} ≤ 1`; and the exceptional set is finite at *every* level, since the moduli
`r ≤ P` are bounded, there are finitely many characters of each such modulus, and a primitive
`L`-function has finitely many zeros in the box `1 - H/log X ≤ re ρ ≤ 1`, `|im ρ| ≤ √X` because its
zero set is discrete there. -/

/-- The zeros of `LFunction χ` for a nontrivial `χ` are finite in any compact set. -/
private theorem finite_zeros_LFunction_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0}).Finite := by
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hdiff
  have hval : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hcod : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0}ᶜ ∈ Filter.codiscrete ℂ :=
    hanalytic.preimage_zero_mem_codiscrete hval
  obtain ⟨hclosed, hdiscrete⟩ := compl_mem_codiscrete_iff.mp hcod
  exact (hS.inter_right hclosed).finite (hdiscrete.mono Set.inter_subset_right)

/-- The zeros of the Riemann zeta function are finite in any compact set. -/
private theorem finite_zeros_riemannZeta {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ {ρ : ℂ | riemannZeta ρ = 0}).Finite :=
  hS.inter_riemannZetaZeros_finite

/-- A zero of a primitive Dirichlet `L`-function has real part at most one. -/
private theorem re_le_one_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) {ρ : ℂ} (hL : DirichletCharacter.LFunction χ ρ = 0) : ρ.re ≤ 1 := by
  by_contra h
  rw [not_le] at h
  rcases eq_or_ne χ 1 with h1 | h1
  · have hN : N = 1 := by
      have hc : DirichletCharacter.conductor χ = N := hprim
      rw [h1, DirichletCharacter.conductor_one] at hc
      exact hc.symm
    obtain rfl : N = 1 := hN
    simp only [DirichletCharacter.LFunction_modOne_eq] at hL
    exact riemannZeta_ne_zero_of_one_le_re h.le hL
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl h1) h.le hL

/-- For a primitive character the zeros of the `L`-function in the box `1 - h ≤ re ≤ 1`,
`|im| ≤ U` are finite. -/
private theorem finite_zeros_in_box {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (h U : ℝ) :
    ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 1 - ρ.re ≤ h ∧ ρ.re ≤ 1 ∧
      |ρ.im| ≤ U}).Finite := by
  have hB : IsCompact (Set.Icc (1 - h) 1 ×ℂ Set.Icc (-U) U) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hZ : (Set.Icc (1 - h) 1 ×ℂ Set.Icc (-U) U ∩
      {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0}).Finite := by
    rcases eq_or_ne χ 1 with h1 | h1
    · have hN : N = 1 := by
        have hc : DirichletCharacter.conductor χ = N := hprim
        rw [h1, DirichletCharacter.conductor_one] at hc
        exact hc.symm
      obtain rfl : N = 1 := hN
      simpa only [DirichletCharacter.LFunction_modOne_eq] using finite_zeros_riemannZeta hB
    · exact finite_zeros_LFunction_of_ne_one χ h1 hB
  refine hZ.subset ?_
  rintro ρ ⟨hL, hre, hre1, him⟩
  exact ⟨Complex.mem_reProdIm.mpr ⟨⟨by linarith, hre1⟩, abs_le.mp him⟩, hL⟩

/-- The exceptional set at any level is finite: the moduli are bounded, there are finitely many
characters of each bounded modulus, and a primitive `L`-function has finitely many zeros in the
box `1 - H/log X ≤ re ρ ≤ 1`, `|im ρ| ≤ U`. -/
private theorem excSet_finite (H U P X : ℝ) : (excSet H U P X).Finite := by
  classical
  set cH : ℝ := H / Real.log X with hcH
  set n : ℕ := ⌊P⌋₊ with hn
  have hins : ({z : ExcPair | IsExcZero H U P X z} : Set ExcPair) ⊆
      (((Finset.range (n + 1)).biUnion (fun r =>
        if hr : r = 0 then ∅ else
          haveI : NeZero r := ⟨hr⟩
          (Finset.univ : Finset (DirichletCharacter ℂ r)).biUnion (fun χ =>
            if hp : χ.IsPrimitive then
              (finite_zeros_in_box χ hp cH U).toFinset.image
                (fun ρ => (⟨r, ⟨hr⟩, χ, ρ⟩ : ExcPair))
            else ∅)) : Finset ExcPair) : Set ExcPair) := by
    intro z hz
    haveI : NeZero z.r := z.hr
    obtain ⟨hzP, hzprim, hzL, hzre, hzim⟩ := hz
    have hzre1 : z.ρ.re ≤ 1 := re_le_one_of_primitive hzprim hzL
    have hzρ : z.ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction z.χ ρ = 0 ∧ 1 - ρ.re ≤ cH ∧
        ρ.re ≤ 1 ∧ |ρ.im| ≤ U} :=
      ⟨hzL, by rw [hcH]; exact hzre, hzre1, hzim⟩
    refine Finset.mem_biUnion.mpr ⟨z.r, ?_, ?_⟩
    · rw [Finset.mem_range, hn]
      exact Nat.lt_succ_of_le (Nat.le_floor hzP)
    · rw [dif_neg (NeZero.ne z.r)]
      haveI : NeZero z.r := z.hr
      refine Finset.mem_biUnion.mpr ⟨z.χ, Finset.mem_univ _, ?_⟩
      rw [dif_pos hzprim]
      exact Finset.mem_image.mpr
        ⟨z.ρ, (finite_zeros_in_box z.χ hzprim cH U).mem_toFinset.mpr hzρ, by cases z; rfl⟩
  have hfin : ({z : ExcPair | IsExcZero H U P X z} : Set ExcPair).Finite :=
    Finset.finite_toSet _ |>.subset hins
  simpa only [excSet] using hfin.insert pole

section Leaf

variable {ε H0 X0 H X P0 : ℝ}

private theorem rpow_neg_le_one {ε A X0 X P0 : ℝ} (hε : 0 < ε)
    (hHyp : Thm1Hyp ε A X0 X P0) : X ^ (-ε) ≤ 1 := by
  obtain ⟨-, hX3, -, -⟩ := hHyp
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

/-- Under the U-1634 range `P₀` is positive: `X^ε L^A > 0` for `X ≥ 3`. -/
private theorem P0_pos {ε A X0 X P0 : ℝ} (hHyp : Thm1Hyp ε A X0 X P0) : 0 < P0 := by
  obtain ⟨-, hX3, hlow, -⟩ := hHyp
  have hX : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hX ε) (Real.rpow_pos_of_pos hL A)) hlow

end Leaf

/-- LEAF arXiv:1804.05561v1 display 8.28: the major arc parameter P exists DECISION U-1614: `0 < ε < 4/9` added, Theorem 1 takes `ε` small, p. 8. The old form is false at
`ε = -1`, `DecompJ665.P_leaf_false`, and at `ε = 1`, `Audit1614.old_leaf_P_exists_large_eps_false`. -/
theorem leaf_P_exists {ε A X0 H X P0 : ℝ} (hε : 0 < ε) (hε' : ε < 4 / 9)
    (hHyp : Thm1Hyp ε A X0 X P0) :
  ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by
  have hx : X ^ (-ε) ≤ 1 := rpow_neg_le_one hε hHyp
  have hP0 : 0 < P0 := P0_pos hHyp
  refine ⟨P0, ?_, le_rfl, excSet_finite H (Real.sqrt X) P0 X⟩
  calc P0 * X ^ (-ε) ≤ P0 * 1 :=
        mul_le_mul_of_nonneg_left hx hP0.le
    _ = P0 := mul_one P0

/-- LEAF arXiv:1804.05561v1 display 9.16: the singular series converges at every positive
frequency. DECISION 2026-10-31 architect PC 20261031T2333Z-383: `0 < m` added; the old form was
false at `m = 0`, LeafAudit168.prime_zero_no_limit. -/
theorem leaf_singular_series_converges (H X P : ℝ) :
  ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by sorry

/- REPAIRED 2026-11-04 lomos 20261104T1614Z: `0 < m` added to the frequency of the bound of
`leaf_main_term_bound` below, the only change of statement in this file. The former form was
refuted at `m = 0`, outside the convergence hypothesis, which constrains `Sg'` only at positive
frequencies: `DecompJ665.main_term_leaf579_false`. At `m = 0` the supplied zero value `Sg' z w 0`
is free while the pole term of `mainTermPrime` is `Sg' pole pole 0` times a nonzero kernel, so no
constant survives; at positive `m` the leaf is display 10.25. `assembly_221` supplies `0 < m` from
its own frequency clause and proves the `m = 0` instance directly. -/

/-! ### The values and sizes of the coefficient at small modulus

`cCoefPrime` is built from the totient, one Ramanujan sum and two Gauss sums. At modulus one all
of them are `1`, so the coefficient is `1`, and the universal finite bound `‖c_q^ψ(m)‖ ≤ q` gives
`‖c'‖ ≤ q^3/φ(q)^2`. That last bound is not summable: `∑ q^3/φ(q)^2` diverges, so it does NOT give
display 9.16. The missing input is the twisted Ramanujan bound `‖c_q^ψ(m)‖ ≪ (m,q)^{1/2} d(q) q^{1/2}`
together with the Gauss sum modulus `‖τ(ψ)‖ = q^{1/2}` for primitive `ψ` and multiplicativity of
`c'` in `q`. -/

/-- The Ramanujan sum at modulus one is `1`, for every character of modulus one. -/
private theorem cRam_one_eq_one (ψ : DirichletCharacter ℂ 1) (m : ℤ) : cRam 1 ψ m = 1 := by
  unfold cRam
  rw [Finset.Icc_self, Finset.sum_singleton]
  have hcast : ((1 : ℕ) : ZMod 1) = 1 := Nat.cast_one
  rw [hcast, MulChar.map_one]
  have harg : ((1 : ℕ) : ℝ) * (m : ℝ) / ((1 : ℕ) : ℝ) = (m : ℝ) := by
    push_cast
    ring
  rw [harg, LeanLab.PNTPort.LargeSieve.e_int, mul_one]

/-- At modulus one the coefficient of the prime singular series is `1`: the totient is `1`, the
Ramanujan sum is `1` and both Gauss sums are `1`. -/
private theorem cCoefPrime_one (z w : ExcPair) (m : ℕ) : cCoefPrime z w 1 m = 1 := by
  have hc : cRam 1 ((lift z 1) * (lift w 1)⁻¹) (-(m : ℤ)) = 1 :=
    cRam_one_eq_one _ _
  have ht : tau 1 ((lift z 1)⁻¹) = 1 := cRam_one_eq_one _ 1
  have ht' : tau 1 ((lift w 1)⁻¹) = 1 := cRam_one_eq_one _ 1
  have hφ : ((Nat.totient 1 : ℂ) ^ 2)⁻¹ = 1 := by
    rw [Nat.totient_one]
    norm_num
  unfold cCoefPrime
  rw [hc]
  rw [ht, ht', map_one, mul_one, mul_one, mul_one, hφ]

/-- The universal finite bound for the Ramanujan sum: at most `q` terms of modulus at most one. -/
private theorem norm_cRam_le {q : ℕ} (ψ : DirichletCharacter ℂ q) (m : ℤ) : ‖cRam q ψ m‖ ≤ (q : ℝ) := by
  have h : cRam q ψ m =
      LeanLab.Pintz2021.CharacterSumsTask53.characterSum (fun h => ψ (h : ZMod q)) q m := by
    unfold cRam LeanLab.Pintz2021.CharacterSumsTask53.characterSum
    rfl
  rw [h]
  exact LeanLab.Pintz2021.CharacterSumsTask53.norm_characterSum_dirichlet ψ m

/-- The same bound for the Gauss sum, which is the Ramanujan sum at frequency one. -/
private theorem norm_tau_le {q : ℕ} (ψ : DirichletCharacter ℂ q) : ‖tau q ψ‖ ≤ (q : ℝ) :=
  norm_cRam_le ψ 1

/-- The crude coefficient bound this file can reach: `‖c'(χ₁,χ₂,q,m)‖ ≤ q³/φ(q)²`. The series
`∑ q³/φ(q)²` diverges, so this bound does not give display 9.16; the missing input is the twisted
Ramanujan bound `‖c_q^ψ(m)‖ ≪ (m,q)^{1/2} d(q) q^{1/2}` with the Gauss sum modulus `‖τ(ψ)‖ = q^{1/2}`
for primitive `ψ`. -/
private theorem norm_cCoefPrime_le (z w : ExcPair) (q m : ℕ) :
    ‖cCoefPrime z w q m‖ ≤ ‖(((Nat.totient q : ℂ)) ^ 2)⁻¹‖ * (q : ℝ) * (q : ℝ) * (q : ℝ) := by
  have h1 : ‖cRam q ((lift z q) * (lift w q)⁻¹) (-(m : ℤ))‖ ≤ (q : ℝ) := norm_cRam_le _ _
  have h2 : ‖tau q ((lift z q)⁻¹)‖ ≤ (q : ℝ) := norm_tau_le _
  have h3 : ‖tau q ((lift w q)⁻¹)‖ ≤ (q : ℝ) := norm_tau_le _
  have h3' : ‖(starRingEnd ℂ) (tau q ((lift w q)⁻¹))‖ ≤ (q : ℝ) := by
    rw [RCLike.norm_conj]
    exact h3
  unfold cCoefPrime
  rw [norm_mul, norm_mul, norm_mul]
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  refine mul_le_mul (mul_le_mul (mul_le_mul (le_refl _) h1 (norm_nonneg _) (norm_nonneg _)) h2
    (norm_nonneg _) (by positivity)) h3' (norm_nonneg _) (by positivity)

/-! ### Reducing `leaf_singular_series_converges` to summability of the coefficients

Display 9.16 asserts that the partial sums of `𝔖'` converge. Everything analytic in that
assertion sits in the coefficients `c'(χ₁,χ₂,q,m)`: if the coefficient series over the multiples
of `[r₁, r₂]` is summable then its partial sums converge, and the limit function can be built by
choice. This is the step that does not need any estimate, and it isolates what does. -/

/-- Convergence of the partial sums of the prime singular series from summability of its
coefficients. -/
private theorem tendsto_singPartialPrime_of_summable (z w : ExcPair) (m : ℕ)
    (h : Summable fun q : ℕ => if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) :
    ∃ L : ℂ, Tendsto (singPartialPrime z w m) atTop (𝓝 L) := by
  classical
  set g : ℕ → ℂ := fun q => if 1 ≤ q ∧ Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0 with hg
  have hsuccf : Summable fun q : ℕ =>
      (if Nat.lcm z.r w.r ∣ q + 1 then cCoefPrime z w (q + 1) m else 0) :=
    (summable_nat_add_iff 1).mpr h
  have hgsucc : Summable fun q : ℕ => g (q + 1) :=
    hsuccf.congr (fun q => by
      rw [hg]
      have hq1 : 1 ≤ q + 1 := Nat.le_add_left 1 q
      simp only [hq1, true_and])
  have hgs : Summable g := (summable_nat_add_iff 1).mp hgsucc
  have hrep : ∀ Q : ℕ, singPartialPrime z w m Q = ∑ q ∈ Finset.range (Q + 1), g q := by
    intro Q
    have hrange : Finset.range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
      ext q
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hzero : (0 : ℕ) ∉ Finset.Icc 1 Q := by simp
    have hg0 : g 0 = 0 := by
      rw [hg]
      simp
    unfold singPartialPrime
    rw [Finset.sum_filter, hrange, Finset.sum_insert hzero, hg0, zero_add]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    rw [hg]
    simp only [hq1, true_and]
  have hlim : Tendsto (fun N : ℕ => ∑ q ∈ Finset.range N, g q) atTop (𝓝 (∑' q, g q)) :=
    hgs.hasSum.tendsto_sum_nat
  have hshift : Tendsto (fun Q : ℕ => ∑ q ∈ Finset.range (Q + 1), g q) atTop (𝓝 (∑' q, g q)) := by
    have hc := hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hfun : ((fun N : ℕ => ∑ q ∈ Finset.range N, g q) ∘ fun a : ℕ => a + 1)
        = fun Q : ℕ => ∑ q ∈ Finset.range (Q + 1), g q := rfl
    rw [hfun] at hc
    exact hc
  refine ⟨∑' q, g q, ?_⟩
  have hrw : singPartialPrime z w m = fun Q => ∑ q ∈ Finset.range (Q + 1), g q := funext hrep
  rw [hrw]
  exact hshift

/-- `leaf_singular_series_converges` follows from summability of the coefficients at every
exceptional pair and every positive frequency; that summability is the analytic input of display
9.16 that this file does not contain. -/
private theorem leaf_singular_series_converges_of_summable (H X P : ℝ)
    (h : ∀ z w : ExcPair, z ∈ excSet H (Real.sqrt X) P X → w ∈ excSet H (Real.sqrt X) P X →
      ∀ m : ℕ, 0 < m →
        Summable fun q : ℕ => if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) :
    ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by
  classical
  refine ⟨fun z w m =>
    if hc : ∃ L : ℂ, Tendsto (singPartialPrime z w m) atTop (𝓝 L) then hc.choose else 0, ?_⟩
  intro z hz w hw m hm
  have hc : ∃ L : ℂ, Tendsto (singPartialPrime z w m) atTop (𝓝 L) :=
    tendsto_singPartialPrime_of_summable z w m (h z w hz hw m hm)
  beta_reduce
  rw [dif_pos hc]
  exact hc.choose_spec

/-- LEAF arXiv:1804.05561v1 display 10.25: the main term error is `O_ε(𝔖(m) X e^{-c_ε H}) +
O_ε(X^{1-ε₀})` for the actual series, with `ε₀` and `c_ε` existential as in Theorem 1.
DECISION 2026-10-31 architect PC 20261031T2333Z-383, replaces two retired leaves above. 
DECISION U-1614: `ε0 ≤ 1/4` added, a smaller `ε0` only weakens the claim for `X ≥ 1`; it discharges
`ε < 4/9` in `leaf_P_exists` without changing `assembly_221`.
DECISION 2026-11-08 architect 20261108T0450Z U-1634: the U-1634 shape of `State1581.Theorem1_220`.
`c, C` are existential before `H`, with an exponent `A ≥ 0`; `H ≥ H₀` is a fixed constant and
`X₀` is chosen after it, Pin1 display 2.8 and the remark after Pin1 display 2.12; the range is
`X^ε L^A ≤ P₀`, Pin1 display 1.8, and `H ≤ (log X)/2` is gone. `ε0 ≤ 1/5` so that the range is
inhabited for every `ε < ε0`, `State1581.thm1Hyp_inhabited`. The old form was false at `P₀ = 1`,
`H = (log X)/2` by hand, PROGRESS.md U-1634.
DECISION 2026-11-08 architect arch20261108T1030Z PMT: two weakenings to match P0054 page 188
Theorem 1, read from the page image. The level `P` is now existential in `[P₀X^{-ε}, P₀]`, after
`P₀`, as the theorem says one can choose such a `P`; the former form asserted the bound at every
`P` of the interval. The second error term is `X^{1-ε}`, the `O_ε(X^{1-ε})` of display 2.21; the
former `X^{1-ε₀}` with `ε < ε₀` is smaller for `X ≥ 1`, so it claimed more than the paper. -/
theorem leaf_main_term_bound :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ 1 / 5 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c C A H0 : ℝ, 0 < c ∧ 0 ≤ A ∧ ∀ H : ℝ, H0 ≤ H → ∃ X0 : ℝ,
      ∀ X P0 : ℝ, Thm1Hyp ε A X0 X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
      ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ X →
        ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
          C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)) := by sorry

/-! ### The zero frequency instance of `assembly_221`

The repaired leaf covers positive frequencies only, and `assembly_221` states its bound at every
`m ≤ X`, `m = 0` included. At `m = 0` the assembly is free to choose the value of its own series,
so it cancels the pole term exactly: it takes `Sg' pole pole 0 = R1majPrime ε X P 0 / K` when the
zero difference kernel `K` is nonzero, and `0` when the kernel vanishes, which happens exactly when
`S` is the zero function. Both cases give a zero left hand side. -/

/-- At the zero frequency the main term of a series supported on the pole pair is the supplied
value times the pole kernel; the same computation as `DecompJ665.mainTerm_zero_supported`,
restated here so this file needs no import of that module. -/
private theorem mainTermPrime_zero_pole (H P X ε : ℝ) (t : ℂ)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) :
    mainTermPrime (excSet H (Real.sqrt X) P X)
      (fun z w m => if m = 0 then (if z = pole ∧ w = pole then t else 0) else Sg z w m)
      ε X 0 = t * WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 0 true := by
  unfold mainTermPrime
  simp only [ite_true]
  simp_rw [finsum_eq_if]
  rw [finsum_eq_single _ pole (by intro z hz; simp [hz])]
  simp only [pole_mem_excSet, ite_true]
  rw [finsum_eq_single _ pole (by intro w hw; simp [hw])]
  simp [pole_mem_excSet, mult_pole, Asign_pole, show pole.ρ = 1 from rfl]

/-- The difference kernel at frequency zero counts the diagonal pairs `(a, a)` with
`X₁ < a ≤ ⌊X⌋`, so it is empty once `⌊X⌋ ≤ X₁`. -/
private theorem kernelPairs_eq_empty_of_le {X1 X : ℝ} (h : (⌊X⌋₊ : ℝ) ≤ X1)
    (m : ℤ) (difference : Bool) : WeightedKernelsTask08.kernelPairs X1 X m difference = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨a, b⟩ hp
  obtain ⟨hp, ha, -⟩ := Finset.mem_filter.mp hp
  have hab : a ≤ ⌊X⌋₊ := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2
  have : (a : ℝ) ≤ X1 := le_trans (by exact_mod_cast hab) h
  exact absurd ha (not_lt.mpr this)

/-- In the range `⌊X⌋ ≤ X₁` the zero frequency pole kernel vanishes. -/
private theorem weightedKernel_zero_eq_zero {X1 X : ℝ} (h : (⌊X⌋₊ : ℝ) ≤ X1) :
    WeightedKernelsTask08.weightedKernel X1 X 1 1 0 true = 0 := by
  unfold WeightedKernelsTask08.weightedKernel
  rw [kernelPairs_eq_empty_of_le h]
  simp

/-- In the range `X₁ < ⌊X⌋` the zero frequency pole kernel is a positive pair count. -/
private theorem weightedKernel_zero_ne_zero {X1 X : ℝ} (h0 : 0 ≤ X1)
    (h : X1 < (⌊X⌋₊ : ℝ)) :
    WeightedKernelsTask08.weightedKernel X1 X 1 1 0 true ≠ 0 := by
  rw [WeightedKernelsTask08.weightedKernel_poles]
  apply Nat.cast_ne_zero.mpr
  apply Finset.card_ne_zero.mpr
  refine ⟨(⌊X⌋₊, ⌊X⌋₊), ?_⟩
  have h1 : 1 ≤ ⌊X⌋₊ := by
    have hpos : (0 : ℝ) < (⌊X⌋₊ : ℝ) := lt_of_le_of_lt h0 h
    exact_mod_cast hpos
  simp [WeightedKernelsTask08.kernelPairs, h, h1]

/-- In the range `⌊X⌋ ≤ X₁` the exponential sum `S` is identically zero, the range `X₁ < n ≤ X`
containing no integer. -/
private theorem S_eq_zero {X1 X : ℝ} (h : (⌊X⌋₊ : ℝ) ≤ X1) : S X1 X = 0 := by
  funext β
  unfold S
  refine Finset.sum_eq_zero fun n hn => ?_
  have hnX : (n : ℝ) ≤ X1 := by
    have hn' : n ≤ ⌊X⌋₊ := by simpa using hn
    exact le_trans (by exact_mod_cast hn') h
  unfold aS
  rw [if_neg (by
    rintro ⟨-, hlt, -⟩
    exact absurd hlt (not_lt.mpr hnX))]
  simp

/-- The minor part of the difference coefficient of the zero function is zero. -/
private theorem differenceR1_zero (mi : Set ℝ) (m : ℕ) :
    differenceR1 (fun _ : ℝ => (0 : ℂ)) mi m = 0 := by
  unfold differenceR1 coef
  simp

/-- With `S` identically zero the zero frequency major arc term vanishes. -/
private theorem R1majPrime_zero_of_S_eq_zero {ε X P : ℝ} (hS : S (X1 ε X) X = 0) :
    R1majPrime ε X P 0 = 0 := by
  unfold R1majPrime
  rw [hS]
  exact differenceR1_zero _ 0

/-- The error scale of display 10.25 is nonnegative as soon as `X ≥ 0`. -/
private theorem sing_error_nonneg {m : ℕ} {X ε0 c H : ℝ} (hX : 0 ≤ X) :
    0 ≤ Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0) :=
  add_nonneg
    (mul_nonneg
      (mul_nonneg (LeanLab.Pintz2021.Applications.Sing_pos m).le hX)
      (Real.exp_pos _).le)
    (Real.rpow_nonneg hX _)

/-- Assembly theorem for P0054 page 8 display 2.21, proved directly from the leaves. Its
convergence clause asks `0 < m` since 2026-10-31, matching DecompJ281.leaf_221.
DECISION 2026-11-08 U-1634: the quantifier shape of `State1581.Theorem1_220`, U-1634 form.
DECISION 2026-11-08 architect arch20261108T1030Z PMT: error term `X^{1-ε}` as in
`State1581.Theorem1_220` and P0054 page 188, following the repaired leaf; `P` is the level the leaf
chooses, finiteness comes from `excSet_finite`. -/
theorem assembly_221 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c C A H0 : ℝ, 0 < c ∧ 0 ≤ A ∧ ∀ H : ℝ, H0 ≤ H → ∃ X0 : ℝ, ∀ X P0 : ℝ,
      Thm1Hyp ε A X0 X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)) := by
  obtain ⟨ε0, hε0, -, h1⟩ := leaf_main_term_bound
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  obtain ⟨c, C, A, H0, hc, hA, hH⟩ := h1 ε hε hε0'
  refine ⟨c, max C 1, A, H0, hc, hA, ?_⟩
  intro H hH0
  obtain ⟨X0, hC⟩ := hH H hH0
  refine ⟨X0, ?_⟩
  intro X P0 hHyp
  obtain ⟨P, hP1, hP2, hCP⟩ := hC X P0 hHyp
  refine ⟨P, hP1, hP2, excSet_finite H (Real.sqrt X) P X, ?_⟩
  obtain ⟨Sg, hSg⟩ := leaf_singular_series_converges H X P
  let A : ℂ := R1majPrime ε X P 0
  let K : ℂ := WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 0 true
  let t : ℂ := if (⌊X⌋₊ : ℝ) ≤ X1 ε X then 0 else A / K
  let Sg' : ExcPair → ExcPair → ℕ → ℂ :=
    fun z w m => if m = 0 then (if z = pole ∧ w = pole then t else 0) else Sg z w m
  refine ⟨Sg', ?_, ?_⟩
  · intro z hz w hw m hm
    have hpt : Sg' z w m = Sg z w m := by
      simp only [Sg', if_neg (Nat.ne_of_gt hm)]
    rw [hpt]
    exact hSg z hz w hw m hm
  · intro m hmX
    by_cases hm : m = 0
    · subst hm
      have hX0 : 0 ≤ X := by
        simpa only [Nat.cast_zero] using hmX
      have htK : t * K = A := by
        by_cases hcut : (⌊X⌋₊ : ℝ) ≤ X1 ε X
        · dsimp only [t]
          rw [if_pos hcut, zero_mul]
          exact (R1majPrime_zero_of_S_eq_zero (S_eq_zero hcut)).symm
        · dsimp only [t]
          rw [if_neg hcut]
          exact div_mul_cancel₀ A
            (weightedKernel_zero_ne_zero (Real.rpow_nonneg hX0 _) (lt_of_not_ge hcut))
      have hmain : mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X 0 = A := by
        rw [mainTermPrime_zero_pole H P X ε t Sg]
        exact htK
      rw [hmain, sub_self, norm_zero]
      exact mul_nonneg (le_trans zero_le_one (le_max_right C 1))
        (sing_error_nonneg hX0)
    · have hm0 : 0 < m := Nat.pos_of_ne_zero hm
      have hX0 : 0 ≤ X := le_trans (by positivity) hmX
      have hmain : mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m =
          mainTermPrime (excSet H (Real.sqrt X) P X) Sg ε X m := by
        simp only [mainTermPrime, Sg', if_neg hm]
      rw [hmain]
      refine le_trans (hCP Sg hSg m hm0 hmX) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sing_error_nonneg hX0)

end
end LeanLab.Pintz2021.DecompJ579

#print axioms LeanLab.Pintz2021.DecompJ579.assembly_221

