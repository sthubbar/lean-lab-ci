import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.DecompJ281
import LeanLab.RieselVaughan1983.GaussImprim

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

/-! ### The singular series: summability of the coefficients

The helper block below is the (sorry-free) development of the sibling unit
`LeanLab/Pintz2021/DecompJ834.lean`, lines 21 to 1244: the Moebius decomposition of the
coefficient sum, the twisted Ramanujan bound on c_psi(m), the induced Gauss bound on
tau_q(ind chi), the totient lower bound, and the majorant q^(-3/2)(1+log q)^2 for |c'|.
Every theorem here is `private`; no declaration of this file changes. -/

section Transfer

open Real
open scoped Topology
open LeanLab.PNTPort.LargeSieve

open Finset LeanLab.PNTPort.LargeSieve

/-! ### Helper lemmas for `leaf_singular_series_converges_3`

All of this is new in this session: the Möbius decomposition of the coefficient sum, the bound
`‖τ_q(ind χ)‖² = conductor`, the twisted Ramanujan bound `‖c_ψ(m)‖ ≤ √r σ(m)`, and the
`q^{-3/2}(1+log q)^2` majorant.  Nothing here changes a statement of the file. -/

noncomputable section



open LeanLab.PNTPort.LargeSieve in
/-- The lab's exponential is periodic in the integer direction. -/
private theorem e_add_int (x : ℝ) (k : ℤ) : e (x + (k : ℝ)) = e x := by
  rw [e_add, e_int, mul_one]

open LeanLab.PNTPort.LargeSieve in
/-- Mathlib's standard additive character on `ZMod q` is the lab's exponential at `x.val/q`. -/
private theorem stdAddChar_eq_e {q : ℕ} [NeZero q] (x : ZMod q) :
    ZMod.stdAddChar x = e ((x.val : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  unfold e
  congr 1
  push_cast
  ring

open LeanLab.PNTPort.LargeSieve in
/-- The standard additive character at a product of residues is the lab's exponential at the
corresponding real frequency. -/
private theorem stdAddChar_mul_eq_e {q : ℕ} [NeZero q] (h : ℕ) (m : ℤ) :
    ZMod.stdAddChar ((h : ZMod q) * (m : ZMod q)) = e ((h : ℝ) * m / q) := by
  rw [stdAddChar_eq_e]
  have hcast : ((((h : ZMod q) * (m : ZMod q)).val : ℤ) : ZMod q) = ((h * m : ℤ) : ZMod q) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    push_cast
    ring
  have hdvd : (q : ℤ) ∣ (h * m) - ((((h : ZMod q) * (m : ZMod q)).val : ℤ)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp hcast
  obtain ⟨k, hk⟩ := hdvd
  have hkR : (h : ℝ) * m - ((((h : ZMod q) * (m : ZMod q)).val : ℤ) : ℝ) = (k : ℝ) * q := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at h ⊢
    linarith
  have hval : ((((h : ZMod q) * (m : ZMod q)).val : ℝ)) = (h : ℝ) * m - (k : ℝ) * q := by
    have h := hkR
    push_cast at h ⊢
    linarith
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have harg : ((((h : ZMod q) * (m : ZMod q)).val : ℝ) / q) =
      (h : ℝ) * m / q + ((-k : ℤ) : ℝ) := by
    rw [hval]
    push_cast
    field_simp
    ring
  rw [harg, e_add_int]


/-- Summing over the residues `0, …, n-1` is summing over `ZMod n`. -/
private theorem sum_range_eq_sum_ZMod {n : ℕ} [NeZero n] (f : ZMod n → ℂ) :
    ∑ j ∈ Finset.range n, f (j : ZMod n) = ∑ a : ZMod n, f a := by
  refine Finset.sum_bij (fun j (_ : j ∈ Finset.range n) => (j : ZMod n)) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a₁ h₁ a₂ h₂ he
    simp only [Finset.mem_range] at h₁ h₂
    have h3 : a₁ ≡ a₂ [MOD n] := (ZMod.natCast_eq_natCast_iff a₁ a₂ n).mp he
    exact h3.eq_of_lt_of_lt h₁ h₂
  · intro b _
    exact ⟨b.val, Finset.mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
  · intro a _; rfl

/-- **Rotation of a primitive Gauss sum against an arbitrary frequency**: the twisted sum of a
primitive character has the size of the Gauss sum, `√r`, for every frequency. -/
private theorem norm_sum_chi_mul_e_le {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (n : ℤ) :
    ‖∑ j ∈ Finset.range r, χ (j : ZMod r) * e ((j : ℝ) * (n : ℝ) / (r : ℝ))‖ ≤ Real.sqrt r := by
  have hsum : (∑ j ∈ Finset.range r, χ (j : ZMod r) * e ((j : ℝ) * (n : ℝ) / (r : ℝ)))
      = ∑ a : ZMod r, χ a * ZMod.stdAddChar (a * (n : ZMod r)) := by
    rw [← sum_range_eq_sum_ZMod (n := r)
      (fun a : ZMod r => χ a * ZMod.stdAddChar (a * (n : ZMod r)))]
    exact Finset.sum_congr rfl fun (j : ℕ) _ => by
      rw [← stdAddChar_mul_eq_e (q := r) j n]
  rw [hsum, ← LeanLab.RieselVaughan1983.GaussImprim.inv_mul_gaussSum_eq hχ (n : ZMod r)]
  refine le_trans (norm_mul_le _ _) ?_
  have h1 : ‖χ⁻¹ (n : ZMod r)‖ ≤ 1 := by
    by_cases hu : IsUnit (n : ZMod r)
    · have := χ⁻¹.unit_norm_eq_one hu.unit
      rw [hu.unit_spec] at this
      rw [this]
    · rw [MulChar.map_nonunit _ hu, norm_zero]
      exact zero_le_one
  have h2 : ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ)‖ = Real.sqrt r := by
    have := LeanLab.RieselVaughan1983.GaussImprim.norm_sq_gaussSum_of_isPrimitive hχ
    have hnn : (0 : ℝ) ≤ ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ)‖ := norm_nonneg _
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), Real.sqrt_nonneg (r : ℝ)]
  rw [h2]
  calc ‖χ⁻¹ (n : ZMod r)‖ * Real.sqrt r ≤ 1 * Real.sqrt r := by
        exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    _ = Real.sqrt r := one_mul _


/-! ### Rectangle reindexing of `range` sums -/

private theorem sum_range_mul_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n : ℕ} (hn : 0 < n)
    (m : ℕ) :
    ∑ a ∈ Finset.range (n * m), f a = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f (j + n * i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
      exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm])

/-- `e θ = 1` forces `θ` to be an integer. -/
private theorem exists_int_of_e_eq_one {x : ℝ} (h : e x = 1) : ∃ n : ℤ, x = n := by
  have h' : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) = 1 := h
  rw [Complex.exp_eq_one_iff] at h'
  obtain ⟨n, hn⟩ := h'
  have him : 2 * Real.pi * x = (n : ℝ) * (2 * Real.pi) := by
    have h1 := congrArg Complex.im hn
    simpa using h1
  refine ⟨n, ?_⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2 : x * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by linarith
  have := mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h2
  rw [this]

/-- The geometric sum vanishes away from the divisibility points. -/
private theorem sum_range_e_div_eq_zero {s : ℕ} (hs : 0 < s) {m : ℤ} (hm : ¬ (s : ℤ) ∣ m) :
    ∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = 0 := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  set θ : ℝ := (m : ℝ) / (s : ℝ) with hθ
  have hterm : ∀ v : ℕ, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = e θ ^ v := by
    intro v
    have hv : (v : ℝ) * (m : ℝ) / (s : ℝ) = (v : ℝ) * θ := by
      simp only [hθ]; field_simp
    rw [hv, e_nat_mul]
  simp_rw [hterm]
  have hpow : e θ ^ s = 1 := by
    rw [← e_nat_mul]
    have h1 : (s : ℝ) * θ = (m : ℝ) := by
      simp only [hθ]; field_simp
    rw [h1, e_int]
  have hne : e θ ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := exists_int_of_e_eq_one h1
    exact hm ⟨k, by
      have : (m : ℝ) = ((s : ℤ) * k : ℤ) := by
        have h2 : (m : ℝ) = (s : ℝ) * θ := by simp only [hθ]; field_simp
        rw [h2, hk]; push_cast; ring
      exact_mod_cast this⟩
  rw [geom_sum_eq hne s, hpow, sub_self, zero_div]

/-- The geometric sum at a divisibility point is the whole length. -/
private theorem sum_range_e_div_eq_card {s : ℕ} (hs : 0 < s) {m : ℤ} (hm : (s : ℤ) ∣ m) :
    ∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = (s : ℂ) := by
  obtain ⟨k, hk⟩ := hm
  have hterm : ∀ v : ℕ, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = 1 := by
    intro v
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have : (v : ℝ) * (m : ℝ) / (s : ℝ) = (v : ℝ) * (k : ℝ) := by
      rw [hk]; push_cast; field_simp
    rw [this]
    have h2 : (v : ℝ) * (k : ℝ) = (((v : ℤ) * k : ℤ) : ℝ) := by push_cast; ring
    rw [h2]
    exact e_int _
  simp_rw [hterm]
  simp

/-- The inner sum factors into the character sums over the residues mod `r` and the geometric
sum over the multiples of `r`. -/
private theorem sum_range_chi_mul_e_factor {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (χ : DirichletCharacter ℂ r) (m : ℤ) :
    ∑ a ∈ Finset.range (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = (∑ j ∈ Finset.range r, χ (j : ZMod r) * e ((j : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
        * (∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ))) := by
  rw [sum_range_mul_range (f := fun a : ℕ =>
    χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))) (n := r) hr s,
    Finset.sum_comm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hchi : ((j + r * i : ℕ) : ZMod r) = (j : ZMod r) := by
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero]
  have he : ((j + r * i : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)
      = (j : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ) + (i : ℝ) * (m : ℝ) / (s : ℝ) := by
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  simp only [hchi, he, e_add, mul_assoc]

/-- **The inner sum at a general level**: it is bounded by `√r` times the length, and it vanishes
unless the level ratio divides the frequency. -/
private theorem norm_sum_range_chi_mul_e_le {r s : ℕ} [NeZero r] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖∑ a ∈ Finset.range (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  have hr : 0 < r := NeZero.pos r
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [sum_range_chi_mul_e_factor hr hs χ m, norm_mul]
  by_cases hd : (s : ℤ) ∣ m
  · rw [ite_eq_left hd]
    obtain ⟨k, hk⟩ := hd
    have harg : ∀ j : ℕ, (j : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)
        = (j : ℝ) * (k : ℝ) / (r : ℝ) := by
      intro j
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      have hm : (m : ℝ) = (s : ℝ) * (k : ℝ) := by
        rw [hk]; push_cast; ring
      rw [hm]
      push_cast
      field_simp
    simp_rw [harg]
    have h2 := norm_sum_chi_mul_e_le hχ k
    have h3 : (∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ))) = (s : ℂ) :=
      sum_range_e_div_eq_card hs ⟨k, hk⟩
    rw [h3, Complex.norm_natCast]
    exact mul_le_mul h2 le_rfl (by positivity) (Real.sqrt_nonneg _)
  · rw [ite_eq_right hd]
    have h0 : (∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ))) = 0 :=
      sum_range_e_div_eq_zero hs hd
    rw [h0, norm_zero, mul_zero]
    simp


/-! ### Möbius bookkeeping -/

open scoped ArithmeticFunction.Moebius in
/-- `∑_{d | n} μ(d) = [n = 1]`. -/
private theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply
    (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ)) (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h, ArithmeticFunction.one_apply]

open scoped ArithmeticFunction.Moebius in
/-- The coprimality indicator as a Möbius sum over the divisors of the gcd. -/
private theorem sum_moebius_gcd (a b : ℕ) :
    ∑ d ∈ (Nat.gcd a b).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      if Nat.Coprime a b then 1 else 0 := by
  have h := sum_moebius_divisors (Nat.gcd a b)
  have h' : ((∑ d ∈ (Nat.gcd a b).divisors, ArithmeticFunction.moebius d : ℤ) : ℂ)
      = ((if Nat.gcd a b = 1 then 1 else 0 : ℤ) : ℂ) := by rw [h]
  push_cast at h'
  rw [h']

/-- Reindexing a sum over the multiples of `d` in `[1, q]`. -/
private theorem sum_Icc_filter_dvd {q d : ℕ} (hd : d ∣ q) (hd0 : 0 < d) (f : ℕ → ℂ) :
    ∑ h ∈ (Finset.Icc 1 q).filter (fun h => d ∣ h), f h
      = ∑ a ∈ Finset.Icc 1 (q / d), f (d * a) := by
  have himg : (Finset.Icc 1 (q / d)).image (fun a => d * a) = (Finset.Icc 1 q).filter (fun h => d ∣ h) := by
    ext h
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      have hqd : d * (q / d) = q := Nat.mul_div_cancel' hd
      refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨a, rfl⟩⟩
    · rintro ⟨⟨hh1, hh2⟩, ⟨a, rfl⟩⟩
      have ha0 : a ≠ 0 := by rintro rfl; simp at hh1
      have hda : d ≤ d * a := Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero ha0)
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · exact Nat.one_le_iff_ne_zero.mpr ha0
      · exact (Nat.le_div_iff_mul_le hd0).mpr (by nlinarith)
  rw [← himg, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd0 hab

/-- The character value at `0` kills the end points, so the `Icc` sum is the `range` sum. -/
private theorem sum_Icc_chi_mul_e_eq_range {r s : ℕ} [NeZero r] (hr2 : 2 ≤ r)
    (χ : DirichletCharacter ℂ r) (m : ℤ) :
    ∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = ∑ a ∈ Finset.range (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
  haveI : Fact (1 < r) := ⟨by omega⟩
  have hzero : χ ((0 : ℕ) : ZMod r) = 0 := by
    have h : ((0 : ℕ) : ZMod r) = 0 := by simp
    rw [h, MulChar.map_zero]
  have hlast : χ (((r * s : ℕ)) : ZMod r) * e (((r * s : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) = 0 := by
    have h1 : ((r * s : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [h1, MulChar.map_zero, zero_mul]
  have hstep : ∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = ∑ a ∈ Finset.range (r * s + 1), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
    rw [← Finset.sum_filter_of_ne (s := Finset.range (r * s + 1))
      (f := fun a => χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
      (p := fun a => 1 ≤ a) ?_]
    · congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨fun h => ⟨Nat.lt_succ_of_le h.2, h.1⟩, fun h => ⟨h.2, Nat.le_of_lt_succ h.1⟩⟩
    · intro a ha hne
      by_contra h1
      have : a = 0 := by
        simp only [Finset.mem_range] at ha
        omega
      exact hne (by rw [this, hzero, zero_mul])
  rw [hstep, Finset.sum_range_succ, hlast, add_zero]

/-- **The inner sum in `Icc` form** (the shape the lab's `cRam` produces). -/
private theorem norm_sum_Icc_chi_mul_e_le {r s : ℕ} [NeZero r] (hr2 : 2 ≤ r) (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  rw [sum_Icc_chi_mul_e_eq_range hr2 χ m]
  exact norm_sum_range_chi_mul_e_le hs hχ m


/-! ### The value of an induced character -/

private theorem changeLevel_apply {n m : ℕ} (hm : n ∣ m) [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ n) (x : ZMod m) :
    (χ.changeLevel hm) x = if IsUnit x then χ (ZMod.castHom hm (ZMod n) x) else 0 := by
  by_cases hu : IsUnit x
  · obtain ⟨u, rfl⟩ := hu
    rw [ite_eq_left (show IsUnit ((u : ZMod m)) from ⟨u, rfl⟩),
      DirichletCharacter.changeLevel_eq_cast_of_dvd]
    simp only [ZMod.castHom_apply]
  · rw [ite_eq_right hu, MulChar.map_nonunit _ hu]

private theorem changeLevel_apply_natCast {n m : ℕ} (hm : n ∣ m) [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ n) (h : ℕ) :
    (χ.changeLevel hm) (h : ZMod m) = if IsUnit (h : ZMod m) then χ (h : ZMod n) else 0 := by
  rw [changeLevel_apply]
  have hcast : ZMod.castHom hm (ZMod n) (h : ZMod m) = (h : ZMod n) := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hm h]
  rw [hcast]

/-! ### Removing the unit condition -/

/-- For a character mod `r` and `r ∣ q`, the induced character's value at `h` is the character
value at `h mod r` when `h` is a unit mod `q` and zero otherwise; the coprimality condition
`(h, q) = 1` may be replaced by `(h, q/r) = 1`. -/
private theorem chi_mul_unit_eq_chi_mul_coprime {r s : ℕ} [NeZero r] [NeZero (r * s)]
    {χ : DirichletCharacter ℂ r} (h : ℕ) :
    χ (h : ZMod r) * (if IsUnit (h : ZMod (r * s)) then (1 : ℂ) else 0)
      = χ (h : ZMod r) * (if Nat.Coprime h s then (1 : ℂ) else 0) := by
  by_cases hχ : χ (h : ZMod r) = 0
  · rw [hχ, zero_mul, zero_mul]
  · have hunit : IsUnit (h : ZMod r) := (MulChar.apply_ne_zero_iff (χ := χ)).mp hχ
    have hcop : Nat.Coprime h r := (ZMod.isUnit_iff_coprime h r).mp hunit
    have key : IsUnit (h : ZMod (r * s)) ↔ Nat.Coprime h s := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
      exact ⟨fun h' => h'.2, fun h' => ⟨hcop, h'⟩⟩
    by_cases h2 : Nat.Coprime h s
    · rw [ite_eq_left (key.mpr h2), ite_eq_left h2]
    · rw [ite_eq_right (fun h1 => h2 (key.mp h1)), ite_eq_right h2]

/-- The divisors of a gcd, as the divisors of the second argument cut down by divisibility of
the first. -/
private theorem divisors_gcd_eq (h s : ℕ) (hs : s ≠ 0) :
    (Nat.gcd h s).divisors = s.divisors.filter (fun d => d ∣ h) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  have hg : Nat.gcd h s ≠ 0 := by
    rintro h0
    exact hs (Nat.gcd_eq_zero_iff.mp h0).2
  constructor
  · rintro ⟨⟨hd1, hd2⟩, -⟩
    exact ⟨⟨hd2, hs⟩, hd1⟩
  · rintro ⟨⟨hd2, -⟩, hd1⟩
    exact ⟨⟨hd1, hd2⟩, hg⟩

/-- The coprimality indicator as a Möbius sum over the divisors of `s` alone. -/
private theorem sum_moebius_of_coprime {h s : ℕ} (hs : s ≠ 0) :
    ∑ d ∈ s.divisors, (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)
      = if Nat.Coprime h s then (1 : ℂ) else 0 := by
  rw [← sum_moebius_gcd h s, ← Finset.sum_filter, divisors_gcd_eq h s hs]

/-! ### The Möbius decomposition of the coefficient sum -/

/-- The value of the induced character against the coprimality indicator. -/
private theorem changeLevel_apply_natCast' {r s : ℕ} [NeZero r] [NeZero (r * s)]
    (χ : DirichletCharacter ℂ r) (h : ℕ) :
    (χ.changeLevel (Nat.dvd_mul_right r s)) (h : ZMod (r * s))
      = χ (h : ZMod r) * (if Nat.Coprime h s then (1 : ℂ) else 0) := by
  rw [changeLevel_apply_natCast]
  have hsplit : (if IsUnit (h : ZMod (r * s)) then χ (h : ZMod r) else 0)
      = χ (h : ZMod r) * (if IsUnit (h : ZMod (r * s)) then (1 : ℂ) else 0) := by
    by_cases hu : IsUnit (h : ZMod (r * s))
    · rw [ite_eq_left hu, ite_eq_left hu, mul_one]
    · rw [ite_eq_right hu, ite_eq_right hu, mul_zero]
  rw [hsplit, chi_mul_unit_eq_chi_mul_coprime]

set_option maxHeartbeats 1000000 in
/-- **The Möbius decomposition**: the coefficient sum of a character induced from level `r` to
level `r * s` is a `μ`-sum over the divisors of `s` of the shifted sums at the reduced levels. -/
private theorem cRam_changeLevel_eq (r s : ℕ) [NeZero r] [NeZero (r * s)] (hs : 0 < s)
    (χ : DirichletCharacter ℂ r) (m : ℤ) :
    cRam (r * s) (χ.changeLevel (Nat.dvd_mul_right r s)) m
      = ∑ d ∈ s.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ (d : ZMod r) *
          ∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
            e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ)) := by
  have hsne : s ≠ 0 := hs.ne'
  have hF : ∀ h : ℕ, (χ.changeLevel (Nat.dvd_mul_right r s)) (h : ZMod (r * s)) *
      e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = χ (h : ZMod r) * (∑ d ∈ s.divisors,
          (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)) *
        e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
    intro h
    rw [changeLevel_apply_natCast' χ h, ← sum_moebius_of_coprime (h := h) hsne]
  have hswap : ∀ h : ℕ, χ (h : ZMod r) * (∑ d ∈ s.divisors,
        (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)) *
        e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = ∑ d ∈ s.divisors, (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) *
          (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))) := by
    intro h
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  unfold cRam
  simp_rw [hF, hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ r * s := Dvd.dvd.mul_left (Nat.dvd_of_mem_divisors hd) r
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hs
  have hqf : ((r * s) / d) * d = r * s := Nat.div_mul_cancel hdvd
  -- turn the indicator into a filter and pull out the Möbius factor
  have hdist : ∀ h : ℕ, (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) *
        (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
      = (if d ∣ h then (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))) else 0) := by
    intro h
    by_cases hdiv : d ∣ h <;> simp [hdiv]
  have hstep : ∑ h ∈ Finset.Icc 1 (r * s),
        (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) *
          (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
      = ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ h ∈ (Finset.Icc 1 (r * s)).filter (fun h => d ∣ h),
            χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
    simp_rw [hdist]
    rw [← Finset.sum_filter, Finset.mul_sum]
  rw [hstep, sum_Icc_filter_dvd hdvd hdpos]
  have hinner : ∑ a ∈ Finset.Icc 1 ((r * s) / d),
        χ ((d * a : ℕ) : ZMod r) * e (((d * a : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = χ (d : ZMod r) * ∑ a ∈ Finset.Icc 1 ((r * s) / d),
          χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hchi : ((d * a : ℕ) : ZMod r) = (d : ZMod r) * (a : ZMod r) := by push_cast; ring
    have hev : ((d * a : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)
        = (a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ) := by
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hrs0 : 0 < r * s := Nat.mul_pos (NeZero.pos r) hs
      have hq0 : 0 < (r * s) / d := Nat.div_pos (Nat.le_of_dvd hrs0 hdvd) hdpos
      have hqR : (((r * s) / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      have hrsR : ((r * s : ℕ) : ℝ) ≠ 0 := by positivity
      have hcast : ((r * s : ℕ) : ℝ) = (((r * s) / d : ℕ) : ℝ) * (d : ℝ) := by
        conv_lhs => rw [← hqf]
        push_cast
        ring
      have h1 : ((d * a : ℕ) : ℝ) = (d : ℝ) * (a : ℝ) := by push_cast; ring
      rw [h1, hcast]
      field_simp
    rw [hchi, hev, map_mul]
    ring
  rw [hinner]
  ring

/-- A character value has norm at most one. -/
private theorem norm_apply_le_one {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (x : ZMod r) :
    ‖χ x‖ ≤ 1 := by
  by_cases hu : IsUnit x
  · have h := χ.unit_norm_eq_one hu.unit
    rw [hu.unit_spec] at h
    rw [h]
  · rw [MulChar.map_nonunit _ hu, norm_zero]
    exact zero_le_one

/-- **The coefficient sum of an induced character is `√r` times a divisor sum.** -/
private theorem norm_cRam_changeLevel_le (r s : ℕ) [NeZero r] [NeZero (r * s)] (hr2 : 2 ≤ r)
    (hs : 0 < s) {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖cRam (r * s) (χ.changeLevel (Nat.dvd_mul_right r s)) m‖
      ≤ Real.sqrt r * ∑ d ∈ s.divisors,
          (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
  have hsne : s ≠ 0 := hs.ne'
  rw [cRam_changeLevel_eq r s hs χ m]
  have hterm : ∀ d ∈ s.divisors,
      ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ (d : ZMod r) *
        ∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
    intro d hd
    have hds : d ∣ s := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hds hs
    have hdvd : d ∣ r * s := Dvd.dvd.mul_left hds r
    have hqf : ((r * s) / d) * d = r * s := Nat.div_mul_cancel hdvd
    have hqd : (r * s) / d = r * (s / d) := by
      have h1 : d * (s / d) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hds
      have h2 : d * ((r * s) / d) = d * (r * (s / d)) := by
        rw [Nat.mul_comm d, hqf]
        calc r * s = r * (d * (s / d)) := by rw [h1]
          _ = d * (r * (s / d)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hdpos h2
    have hs' : 0 < s / d := Nat.div_pos (Nat.le_of_dvd hs hds) hdpos
    have h3 : ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      rw [hqd]
      exact norm_sum_Icc_chi_mul_e_le hr2 hs' hχ m
    refine le_trans (norm_mul_le _ _) ?_
    rw [norm_mul]
    have h1 : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.cast_one]
      exact Int.cast_le.mpr ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖χ (d : ZMod r)‖ ≤ 1 := norm_apply_le_one χ _
    have hnn : (0 : ℝ) ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      refine mul_nonneg (Real.sqrt_nonneg _) ?_
      split_ifs with h
      · positivity
      · exact le_rfl
    calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖χ (d : ZMod r)‖ *
          ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
            e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ 1 * 1 * (Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0)) := by
          refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) ?_
          positivity
      _ = Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by ring
  refine le_trans (norm_sum_le_of_le _ hterm) ?_
  rw [Finset.mul_sum]


/-! ### The level-one case and the unified inner bound -/

/-- At level one the inner sum is a geometric sum. -/
private theorem sum_Icc_one_eq (s : ℕ) (hs : 0 < s) (m : ℤ) :
    ∑ a ∈ Finset.Icc 1 s, e ((a : ℝ) * (m : ℝ) / (s : ℝ))
      = e ((m : ℝ) / (s : ℝ)) * ∑ b ∈ Finset.range s, e ((b : ℝ) * (m : ℝ) / (s : ℝ)) := by
  have hIcc : Finset.Icc 1 s = Finset.Ico 1 (s + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsub : s + 1 - 1 = s := by omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range, hsub, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have harg : ((1 + b : ℕ) : ℝ) * (m : ℝ) / (s : ℝ)
      = (m : ℝ) / (s : ℝ) + (b : ℝ) * (m : ℝ) / (s : ℝ) := by
    push_cast
    ring
  rw [harg, e_add]

private theorem norm_sum_Icc_one_le (s : ℕ) (hs : 0 < s) (m : ℤ) :
    ‖∑ a ∈ Finset.Icc 1 s, e ((a : ℝ) * (m : ℝ) / (s : ℝ))‖
      ≤ Real.sqrt 1 * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  rw [Real.sqrt_one, one_mul, sum_Icc_one_eq s hs m, norm_mul, norm_e, one_mul]
  by_cases hd : (s : ℤ) ∣ m
  · rw [ite_eq_left hd, sum_range_e_div_eq_card hs hd, Complex.norm_natCast]
  · rw [ite_eq_right hd, sum_range_e_div_eq_zero hs hd, norm_zero]

/-- **The inner sum, level one included.** -/
private theorem norm_sum_Icc_chi_mul_e_le' {r s : ℕ} [NeZero r] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  by_cases hr1 : r = 1
  · subst hr1
    haveI : Subsingleton (ZMod 1) := inferInstance
    have hfun : (fun a : ℕ => χ (a : ZMod 1) * e ((a : ℝ) * (m : ℝ) / (((1 * s : ℕ)) : ℝ)))
        = (fun a : ℕ => e ((a : ℝ) * (m : ℝ) / (s : ℝ))) := by
      funext a
      have h1 : χ (a : ZMod 1) = 1 := by
        rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ 1, map_one]
      have h2 : (((1 * s : ℕ)) : ℝ) = (s : ℝ) := by push_cast; ring
      rw [h1, one_mul, h2]
    rw [hfun, Nat.one_mul]
    simpa using norm_sum_Icc_one_le s hs m
  · have hr2 : 2 ≤ r := by
      have h1 : 0 < r := NeZero.pos r
      omega
    exact norm_sum_Icc_chi_mul_e_le hr2 hs hχ m

/-- **The coefficient sum of an induced character, level one included.** -/
private theorem norm_cRam_changeLevel_le' (r s : ℕ) [NeZero r] [NeZero (r * s)] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖cRam (r * s) (χ.changeLevel (Nat.dvd_mul_right r s)) m‖
      ≤ Real.sqrt r * ∑ d ∈ s.divisors,
          (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
  rw [cRam_changeLevel_eq r s hs χ m]
  have hterm : ∀ d ∈ s.divisors,
      ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ (d : ZMod r) *
        ∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
    intro d hd
    have hds : d ∣ s := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hds hs
    have hdvd : d ∣ r * s := Dvd.dvd.mul_left hds r
    have hqf : ((r * s) / d) * d = r * s := Nat.div_mul_cancel hdvd
    have hqd : (r * s) / d = r * (s / d) := by
      have h1 : d * (s / d) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hds
      have h2 : d * ((r * s) / d) = d * (r * (s / d)) := by
        rw [Nat.mul_comm d, hqf]
        calc r * s = r * (d * (s / d)) := by rw [h1]
          _ = d * (r * (s / d)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hdpos h2
    have hs' : 0 < s / d := Nat.div_pos (Nat.le_of_dvd hs hds) hdpos
    have h3 : ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      rw [hqd]
      exact norm_sum_Icc_chi_mul_e_le' hs' hχ m
    have h1 : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.cast_one]
      exact Int.cast_le.mpr ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖χ (d : ZMod r)‖ ≤ 1 := norm_apply_le_one χ _
    have hnn : (0 : ℝ) ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      refine mul_nonneg (Real.sqrt_nonneg _) ?_
      split_ifs with h
      · positivity
      · exact le_rfl
    refine le_trans (norm_mul_le _ _) ?_
    rw [norm_mul]
    calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖χ (d : ZMod r)‖ *
          ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
            e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ 1 * 1 * (Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0)) := by
          refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) ?_
          positivity
      _ = Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by ring
  refine le_trans (norm_sum_le_of_le _ hterm) ?_
  rw [Finset.mul_sum]

/-- The `m = 1` case: the Gauss sum of an induced character has the size of the conductor. -/
private theorem norm_tau_changeLevel_le (r s : ℕ) [NeZero r] [NeZero (r * s)] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) :
    ‖tau (r * s) (χ.changeLevel (Nat.dvd_mul_right r s))‖ ≤ Real.sqrt r := by
  have h := norm_cRam_changeLevel_le' r s hs hχ (1 : ℤ)
  have h0 : ∀ b ∈ s.divisors,
      b ≠ s → (if ((s / b : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / b : ℕ) : ℝ) else 0) = 0 := by
    intro d hd hds
    have hds' : d ∣ s := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hds' hs
    have hne : s / d ≠ 1 := by
      intro h1
      have h2 : d * (s / d) = d * 1 := by rw [h1]
      rw [Nat.mul_comm d, Nat.div_mul_cancel hds', mul_one] at h2
      exact hds h2.symm
    have : ¬ ((s / d : ℕ) : ℤ) ∣ (1 : ℤ) := by
      intro hdvd
      have h2 : (s / d : ℕ) ∣ 1 := by exact_mod_cast hdvd
      exact hne (Nat.dvd_one.mp h2)
    rw [ite_eq_right this]
  have h1 : s ∉ s.divisors →
      (if ((s / s : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / s : ℕ) : ℝ) else 0) = 0 := by
    intro hnot
    exact absurd (Nat.mem_divisors_self s hs.ne') hnot
  have hsum : ∑ d ∈ s.divisors,
      (if ((s / d : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / d : ℕ) : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (s := s.divisors)
      (f := fun d => (if ((s / d : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / d : ℕ) : ℝ) else 0)) s h0 h1,
      Nat.div_self hs]
    norm_num
  rw [hsum, mul_one] at h
  simpa only [tau] using h


/-! ### The divisor sum and the inverse character -/

/-- The divisor sum of the induced-character bound is at most the sum of the divisors of `m`. -/
private theorem sum_ite_dvd_le_divisors_sum {s m : ℕ} (hm : 0 < m) :
    ∑ d ∈ s.divisors, (if ((s / d : ℕ) : ℤ) ∣ (m : ℤ) then ((s / d : ℕ) : ℝ) else 0)
      ≤ ∑ e ∈ m.divisors, (e : ℝ) := by
  have hinj : ∀ a ∈ s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ)),
      ∀ b ∈ s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ)),
      s / a = s / b → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    have hda : a ∣ s := Nat.dvd_of_mem_divisors ha.1
    have hdb : b ∣ s := Nat.dvd_of_mem_divisors hb.1
    have hsne : s ≠ 0 := (Nat.mem_divisors.mp ha.1).2
    have hspos : 0 < s := Nat.pos_of_ne_zero hsne
    have h1 : a * (s / a) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hda
    have h2 : b * (s / b) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdb
    have hsa : 0 < s / a := Nat.div_pos (Nat.le_of_dvd hspos hda) (Nat.pos_of_dvd_of_pos hda hspos)
    have hkey : a * (s / a) = b * (s / a) := by rw [h1, hab, h2]
    exact Nat.eq_of_mul_eq_mul_right hsa hkey
  rw [← Finset.sum_filter]
  rw [show (∑ d ∈ s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ)), ((s / d : ℕ) : ℝ))
      = ∑ e ∈ (s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ))).image
          (fun d => s / d), (e : ℝ) from by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj a ha b hb hab]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro e he
    simp only [Finset.mem_image, Finset.mem_filter] at he
    obtain ⟨d, ⟨hd, hdvd⟩, rfl⟩ := he
    have hdm : (s / d : ℕ) ∣ m := by exact_mod_cast hdvd
    exact Nat.mem_divisors.mpr ⟨hdm, hm.ne'⟩
  · intro e _ _
    exact Nat.cast_nonneg e

/-- An inverse character factors through the same levels. -/
private theorem factorsThrough_inv {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} {d : ℕ}
    (h : χ⁻¹.FactorsThrough d) : χ.FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  refine ⟨hd, χ₀⁻¹, ?_⟩
  have hinv := congrArg (fun y : DirichletCharacter ℂ n => y⁻¹) hχ
  rw [inv_inv, ← map_inv] at hinv
  exact hinv

private theorem factorsThrough_inv_iff {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} {d : ℕ} :
    χ⁻¹.FactorsThrough d ↔ χ.FactorsThrough d := by
  constructor
  · exact factorsThrough_inv
  · intro h
    exact factorsThrough_inv (χ := χ⁻¹) (by simpa using h)

private theorem conductor_inv {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    (χ⁻¹).conductor = χ.conductor := by
  have h1 : (χ⁻¹).conductor ∣ χ.conductor :=
    (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ := χ⁻¹) (d := χ.conductor)
      χ.conductor_dvd_level).mp (factorsThrough_inv_iff.mpr χ.factorsThrough_conductor)
  have h2 : χ.conductor ∣ (χ⁻¹).conductor :=
    (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ := χ) (d := (χ⁻¹).conductor)
      (χ⁻¹).conductor_dvd_level).mp (factorsThrough_inv_iff.mp (χ⁻¹).factorsThrough_conductor)
  exact Nat.dvd_antisymm h1 h2

private theorem isPrimitive_inv {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r} (h : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def] at h ⊢
  rw [conductor_inv]
  exact h

/-- A product of characters that both factor through `d` factors through `d`. -/
private theorem factorsThrough_mul {n : ℕ} [NeZero n] {χ ψ : DirichletCharacter ℂ n} {d : ℕ}
    (hχ : χ.FactorsThrough d) (hψ : ψ.FactorsThrough d) : (χ * ψ).FactorsThrough d := by
  obtain ⟨hd, χ₀, rfl⟩ := hχ
  obtain ⟨hd', ψ₀, rfl⟩ := hψ
  exact ⟨hd, χ₀ * ψ₀, by rw [map_mul]⟩

/-- The conductor of a product of characters that factor through `L` divides `L`. -/
private theorem conductor_mul_dvd {n L : ℕ} [NeZero n] {χ ψ : DirichletCharacter ℂ n}
    (hL : L ∣ n) (hχ : χ.FactorsThrough L) (hψ : ψ.FactorsThrough L) :
    (χ * ψ).conductor ∣ L :=
  (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ := χ * ψ) (d := L) hL).mp
    (factorsThrough_mul hχ hψ)


/-! ### The majorant and the totient lower bound (ported from the earlier sessions) -/


private theorem log_natCast_le_eight_rpow {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h8 : (0 : ℝ) < (n : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hkey : Real.log (n : ℝ) = 8 * Real.log ((n : ℝ) ^ (1 / 8 : ℝ)) := by
    rw [Real.log_rpow hpos (1 / 8)]
    ring
  rw [hkey]
  have := Real.log_le_sub_one_of_pos h8
  linarith

private theorem one_add_log_sq_le_rpow {n : ℕ} (hn : 1 ≤ n) :
    (1 + Real.log (n : ℝ)) ^ 2 ≤ 81 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hX1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hXpos : (0 : ℝ) < (n : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hlog : Real.log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := log_natCast_le_eight_rpow hn
  have hnn : (0 : ℝ) ≤ 1 + Real.log (n : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
    linarith
  have h9 : (0 : ℝ) ≤ 9 * (n : ℝ) ^ (1 / 8 : ℝ) := by positivity
  have hle : 1 + Real.log (n : ℝ) ≤ 9 * (n : ℝ) ^ (1 / 8 : ℝ) := by linarith
  have h2 : (1 + Real.log (n : ℝ)) ^ 2 ≤ (9 * (n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hnn hle 2
  have hsq : ((n : ℝ) ^ (1 / 8 : ℝ)) * ((n : ℝ) ^ (1 / 8 : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  calc (1 + Real.log (n : ℝ)) ^ 2 ≤ (9 * (n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := h2
    _ = 81 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        have hsq' : ((n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [pow_two, hsq]
        rw [mul_pow, hsq']
        norm_num

open LeanLab.PNTPort.LargeSieve in
private theorem summable_nat_rpow_mul_one_add_log_sq :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (n : ℝ)) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (81 : ℝ) * (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ))) := by
    have h := (summable_nat_add_iff 1).mpr
      ((summable_nat_rpow.mpr (by norm_num : -(5 / 4 : ℝ) < -1)).mul_left (81 : ℝ))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_norm_bounded (g := fun n : ℕ =>
    (81 : ℝ) * (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ))) hbase ?_
  intro n
  have hn : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hpos.le _) (sq_nonneg _))]
  have hlog := one_add_log_sq_le_rpow hn
  have hkey : (((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) * ((((n + 1 : ℕ)) : ℝ) ^ (1 / 4 : ℝ)) =
      (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hpos]
    norm_num
  calc (((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (((n + 1 : ℕ)) : ℝ)) ^ 2
      ≤ (((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) *
          (81 * (((n + 1 : ℕ)) : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hpos.le _)
    _ = 81 * ((((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((n + 1 : ℕ)) : ℝ) ^ (1 / 4 : ℝ)) := by ring
    _ = 81 * (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [hkey]

/-! ### From the pointwise bound to the leaf -/

/-- The product bound: `∏ p ≤ (|s| + 1) ∏ (p - 1)`, i.e. `∏ p/(p - 1) ≤ |s| + 1`. Induction on the maximum element:
removing `a` leaves `|s| - 1` elements, all `≥ 2` and `< a`, so `a ≥ |s| + 1`, and `a ≥ |s| + 1` is
exactly what `a·|s| ≤ (|s| + 1)(a - 1)` needs. -/
private theorem prod_le_card_succ_mul_prod_pred {s : Finset ℕ} (h2 : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  revert h2
  refine Finset.induction_on_max s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h2
    have h2a : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
    have han : a ∉ s := fun h => absurd (ha a h) (lt_irrefl a)
    have hP := ih h2s
    have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨h2s x hx, by have := ha x hx; omega⟩
    have hcard : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have ham : s.card + 2 ≤ a := by omega
    obtain ⟨t, ht⟩ : ∃ t, a = s.card + 2 + t := ⟨a - (s.card + 2), by omega⟩
    have ha1 : a - 1 = s.card + 1 + t := by omega
    rw [Finset.prod_insert han, Finset.prod_insert han, Finset.card_insert_of_notMem han, ha1, ht]
    calc (s.card + 2 + t) * ∏ p ∈ s, p
        ≤ (s.card + 2 + t) * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
          Nat.mul_le_mul_left _ hP
      _ = ((s.card + 2 + t) * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by ring
      _ ≤ ((s.card + 1 + 1) * (s.card + 1 + t)) * ∏ p ∈ s, (p - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          nlinarith
      _ = (s.card + 1 + 1) * ((s.card + 1 + t) * ∏ p ∈ s, (p - 1)) := by ring

/-- `n ≤ φ(n) * (number of distinct prime divisors of n + 1)`. -/
private theorem totient_mul_card_succ_ge (n : ℕ) :
    n ≤ Nat.totient n * (n.primeFactors.card + 1) := by
  have hid := Nat.totient_mul_prod_primeFactors n
  have hP : ∏ p ∈ n.primeFactors, p ≤
      (n.primeFactors.card + 1) * ∏ p ∈ n.primeFactors, (p - 1) :=
    prod_le_card_succ_mul_prod_pred fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * (n.primeFactors.card + 1)) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * ((n.primeFactors.card + 1) *
            ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hP
      _ = (Nat.totient n * (n.primeFactors.card + 1)) *
            ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

private theorem totient_ge_div_card_succ (n : ℕ) :
    (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) ≤ (Nat.totient n : ℝ) := by
  have h := totient_mul_card_succ_ge n
  have hc : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hc]
  have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * ((n.primeFactors.card : ℝ) + 1) := by
    exact_mod_cast h
  linarith

private theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, 2 ≤ p) → 2 ^ s.card ≤ ∏ p ∈ s, p := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro hs
        have h2a : 2 ≤ a := hs a (Finset.mem_insert_self a s)
        have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
        calc 2 ^ s.card * 2 ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul (ih h2s) h2a
          _ = a * ∏ p ∈ s, p := by ring
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    key _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : 0 < n := by omega
  exact h1.trans (Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd n))

private theorem card_primeFactors_le_log_div {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 := two_pow_card_primeFactors_le hn
  have h2' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast h2
  have hbase : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hlog := Real.log_le_log hbase h2'
  rw [Real.log_pow] at hlog
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  linarith

/-- **`φ(n) ≫ n / log n`**: `log 2 · n / (1 + log n) ≤ φ(n)` for `n ≥ 1`, the shape the coefficient
bound `‖c'‖ ≪ q^{-3/2} (1 + log q)^2` needs. -/
private theorem totient_ge_log_two_mul_div {n : ℕ} (hn : 1 ≤ n) :
    Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤ (Nat.totient n : ℝ) := by
  have hφ := totient_ge_div_card_succ n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlog1 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := card_primeFactors_le_log_div hn
  -- `k + 1 ≤ (1 + log n) / log 2`
  have hk2 : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [le_div_iff₀ hlog2] at hk
    linarith
  have hk1 : ((n.primeFactors.card : ℝ) + 1) * Real.log 2 ≤ 1 + Real.log n := by
    nlinarith [hk2, hlog2lt]
  have hone : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  -- `log 2 · n / (1 + log n) ≤ n / (k + 1)`
  have hstep : Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤
      (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + Real.log n) hone]
    nlinarith [hk1, hnpos, hlog2]
  exact hstep.trans hφ

/-! ### The repaired truncation leaf reduced to the discarded-pair mass

`DecompJ665.actual_truncation_error_le_mass` already says the truncation error is at most `X` times
the multiplicity and series weighted mass of the pairs that `Truncation168.retainedPairs` discards.
What is left for `leaf_truncation_error_3` is the estimate of that mass by
`C' * Sing m * X * log U / sqrt U`.  The statement below is exactly that estimate, and the theorem
after it derives the repaired leaf from it, so the analytic content is visible in one place. -/

attribute [local instance] Classical.propDecidable


/-! ### The induced lift and its inverse -/


/-- **The induced-character bound at an arbitrary level**, with the level ratio `q / r`. -/
private theorem norm_cRam_changeLevel_gen {r q : ℕ} [NeZero r] [NeZero q] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (h : r ∣ q) (m : ℤ) :
    ‖cRam q (χ.changeLevel h) m‖
      ≤ Real.sqrt r * ∑ d ∈ (q / r).divisors,
          (if (((q / r) / d : ℕ) : ℤ) ∣ m then (((q / r) / d : ℕ) : ℝ) else 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, q = r * s := ⟨q / r, (Nat.mul_div_cancel' h).symm⟩
  have hq0 : 0 < r * s := NeZero.pos (r * s)
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, Nat.mul_zero] at hq0
      exact absurd hq0 (lt_irrefl 0)
    · exact h0
  have h' : h = Nat.dvd_mul_right r s := Subsingleton.elim _ _
  have hqr : (r * s) / r = s := Nat.mul_div_right s (NeZero.pos r)
  rw [h', hqr]
  exact norm_cRam_changeLevel_le' r s hs hχ m

/-- **The Gauss sum of an induced character at an arbitrary level.** -/
private theorem lift_eq_changeLevel' (z : ExcPair) {q : ℕ} (hq : z.r ∣ q) :
    lift z q = DirichletCharacter.changeLevel hq z.χ := by
  unfold LeanLab.Pintz2021.State1581.lift
  rw [dif_pos hq]

private theorem norm_tau_changeLevel_gen {r q : ℕ} [NeZero r] [NeZero q] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (h : r ∣ q) :
    ‖tau q (χ.changeLevel h)‖ ≤ Real.sqrt (r : ℝ) := by
  obtain ⟨s, rfl⟩ : ∃ s, q = r * s := ⟨q / r, (Nat.mul_div_cancel' h).symm⟩
  have hq0 : 0 < r * s := NeZero.pos (r * s)
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, Nat.mul_zero] at hq0
      exact absurd hq0 (lt_irrefl 0)
    · exact h0
  have h' : h = Nat.dvd_mul_right r s := Subsingleton.elim _ _
  rw [h']
  exact norm_tau_changeLevel_le r s hs hχ

/-- The Gauss sum of the inverse lift has the size of the conductor. -/
private theorem norm_tau_lift_inv_le (z : ExcPair) (hz : z.χ.IsPrimitive) (q : ℕ) (hq : 0 < q)
    (hqr : z.r ∣ q) :
    ‖tau q (lift z q)⁻¹‖ ≤ Real.sqrt (z.r : ℝ) := by
  haveI : NeZero z.r := z.hr
  haveI : NeZero q := ⟨hq.ne'⟩
  rw [lift_eq_changeLevel' z hqr, ← map_inv]
  exact norm_tau_changeLevel_gen (isPrimitive_inv hz) hqr

/-- The coefficient sum of the product of a lift and an inverse lift. -/
private theorem norm_cRam_lift_product_le (z w : ExcPair) (hz : z.χ.IsPrimitive)
    (hw : w.χ.IsPrimitive) (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 0 < q)
    (hL : Nat.lcm z.r w.r ∣ q) :
    ‖cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ))‖
      ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) := by
  haveI : NeZero z.r := z.hr
  haveI : NeZero w.r := w.hr
  haveI : NeZero q := ⟨hq.ne'⟩
  have hL0 : 0 < Nat.lcm z.r w.r := Nat.lcm_pos (NeZero.pos z.r) (NeZero.pos w.r)
  haveI : NeZero (Nat.lcm z.r w.r) := ⟨hL0.ne'⟩
  have hqr1 : z.r ∣ q := (Nat.dvd_lcm_left z.r w.r).trans hL
  have hqr2 : w.r ∣ q := (Nat.dvd_lcm_right z.r w.r).trans hL
  have hf1 : (lift z q).FactorsThrough (Nat.lcm z.r w.r) := by
    rw [lift_eq_changeLevel' z hqr1]
    exact DirichletCharacter.FactorsThrough.mono _
      (DirichletCharacter.changeLevel_factorsThrough z.χ hqr1)
      (Nat.dvd_lcm_left z.r w.r) hL
  have hf2 : ((lift w q)⁻¹).FactorsThrough (Nat.lcm z.r w.r) := by
    rw [lift_eq_changeLevel' w hqr2, ← map_inv]
    exact DirichletCharacter.FactorsThrough.mono _
      (DirichletCharacter.changeLevel_factorsThrough w.χ⁻¹ hqr2)
      (Nat.dvd_lcm_right z.r w.r) hL
  set ψ : DirichletCharacter ℂ q := lift z q * (lift w q)⁻¹ with hψdef
  have hcond : ψ.conductor ∣ Nat.lcm z.r w.r := conductor_mul_dvd hL hf1 hf2
  have hcondq : ψ.conductor ∣ q := hcond.trans hL
  have hcond0 : ψ.conductor ≠ 0 := ψ.conductor_ne_zero
  have hψpc : DirichletCharacter.changeLevel hcondq ψ.primitiveCharacter = ψ :=
    ψ.changeLevel_primitiveCharacter
  have hcr : ‖cRam q ψ (-(m : ℤ))‖ ≤ Real.sqrt (ψ.conductor : ℝ) *
      ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ (-(m : ℤ)) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0) := by
    have e : ‖cRam q ψ (-(m : ℤ))‖
        = ‖cRam q (DirichletCharacter.changeLevel hcondq ψ.primitiveCharacter) (-(m : ℤ))‖ := by
      rw [hψpc]
    rw [e]
    exact norm_cRam_changeLevel_gen ψ.primitiveCharacter_isPrimitive hcondq (-(m : ℤ))
  have hsum_eq : ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ (-(m : ℤ)) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0)
      = ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hdv : (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ)
    · rw [ite_eq_left (by rwa [Int.dvd_neg] : (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ -((m : ℕ) : ℤ)),
        ite_eq_left hdv]
    · rw [ite_eq_right (fun hh => hdv (by rwa [Int.dvd_neg] at hh)), ite_eq_right hdv]
  rw [hsum_eq] at hcr
  have hσ : ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0)
      ≤ ∑ e ∈ m.divisors, (e : ℝ) := sum_ite_dvd_le_divisors_sum hm
  have hsqrt : Real.sqrt (ψ.conductor : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast Nat.le_of_dvd hL0 hcond
  have hnn : (0 : ℝ) ≤ ∑ e ∈ m.divisors, (e : ℝ) := by positivity
  calc ‖cRam q ψ (-(m : ℤ))‖
      ≤ Real.sqrt (ψ.conductor : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) := by
        refine le_trans hcr ?_
        exact mul_le_mul_of_nonneg_left hσ (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt hnn


/-- **The coefficient bound**: `‖c'(z,w,q,m)‖ ≪ q^{-3/2} (1 + log q)^2`, uniformly in `q` on the
multiples of the lcm of the conductors. -/
private theorem norm_cCoefPrime_le_gen (z w : ExcPair) (hz : z.χ.IsPrimitive) (hw : w.χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 1 ≤ q) (hL : Nat.lcm z.r w.r ∣ q) :
    ‖cCoefPrime z w q m‖ ≤
      ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 /
        (Real.log 2) ^ 2) * ((q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2) := by
  have hq0 : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  haveI : NeZero q := ⟨hq0.ne'⟩
  haveI : NeZero z.r := z.hr
  haveI : NeZero w.r := w.hr
  have hL0 : 0 < Nat.lcm z.r w.r := Nat.lcm_pos (NeZero.pos z.r) (NeZero.pos w.r)
  obtain ⟨h1, h2, h3⟩ : ‖cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ))‖ ≤
        Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) ∧
      ‖tau q (lift z q)⁻¹‖ ≤ Real.sqrt (z.r : ℝ) ∧
      ‖tau q (lift w q)⁻¹‖ ≤ Real.sqrt (w.r : ℝ) :=
    ⟨norm_cRam_lift_product_le z w hz hw m hm q hq0 hL,
     norm_tau_lift_inv_le z hz q hq0 ((Nat.dvd_lcm_left z.r w.r).trans hL),
     norm_tau_lift_inv_le w hw q hq0 ((Nat.dvd_lcm_right z.r w.r).trans hL)⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : (0 : ℝ) < 1 + Real.log (q : ℝ) := by
    have := Real.log_nonneg hq1
    linarith
  have hσ : (0 : ℝ) ≤ ∑ e ∈ m.divisors, (e : ℝ) := by positivity
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have := Nat.totient_pos.mpr hq0
    exact_mod_cast this
  have hφlow : Real.log 2 * (q : ℝ) / (1 + Real.log (q : ℝ)) ≤ (Nat.totient q : ℝ) :=
    totient_ge_log_two_mul_div hq
  have hφlow0 : (0 : ℝ) < Real.log 2 * (q : ℝ) / (1 + Real.log (q : ℝ)) := by positivity
  have hφnorm : ‖((Nat.totient q : ℂ) ^ 2)⁻¹‖ = (((Nat.totient q : ℝ)) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  have hrec : 1 / (Nat.totient q : ℝ) ≤ (1 + Real.log (q : ℝ)) / (Real.log 2 * (q : ℝ)) := by
    rw [div_le_div_iff₀ hφpos (by positivity : (0 : ℝ) < Real.log 2 * (q : ℝ)), one_mul]
    have hmul := mul_le_mul_of_nonneg_right hφlow hlogq.le
    have hsimp : Real.log 2 * (q : ℝ) / (1 + Real.log (q : ℝ)) * (1 + Real.log (q : ℝ))
        = Real.log 2 * (q : ℝ) := by field_simp
    rw [hsimp] at hmul
    linarith
  have hφbound : (((Nat.totient q : ℝ)) ^ 2)⁻¹ ≤
      (1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2) := by
    have hsq : (1 / (Nat.totient q : ℝ)) ^ 2 ≤
        ((1 + Real.log (q : ℝ)) / (Real.log 2 * (q : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hrec 2
    have hrhs : ((1 + Real.log (q : ℝ)) / (Real.log 2 * (q : ℝ))) ^ 2
        = (1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2) := by
      rw [div_pow, mul_pow]
    rw [hrhs] at hsq
    calc (((Nat.totient q : ℝ)) ^ 2)⁻¹ = (1 / (Nat.totient q : ℝ)) ^ 2 := by
          rw [one_div, inv_pow]
      _ ≤ _ := hsq
  have hprod : ‖cCoefPrime z w q m‖ ≤ (((Nat.totient q : ℝ)) ^ 2)⁻¹ *
      ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ)) := by
    rw [cCoefPrime, norm_mul, norm_mul, norm_mul]
    rw [show (starRingEnd ℂ) (tau q (lift w q)⁻¹) = star (tau q (lift w q)⁻¹) from rfl, norm_star]
    rw [hφnorm]
    have hsqr1 : Real.sqrt (z.r : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast Nat.le_of_dvd hL0 (Nat.dvd_lcm_left z.r w.r)
    have hsqr2 : Real.sqrt (w.r : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast Nat.le_of_dvd hL0 (Nat.dvd_lcm_right z.r w.r)
    have hLnn : (0 : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := Real.sqrt_nonneg _
    have ht1 : ‖tau q (lift z q)⁻¹‖ ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := le_trans h2 hsqr1
    have ht2 : ‖tau q (lift w q)⁻¹‖ ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := le_trans h3 hsqr2
    have hφnn : (0 : ℝ) ≤ (((Nat.totient q : ℝ)) ^ 2)⁻¹ := by positivity
    calc (((((Nat.totient q : ℝ)) ^ 2)⁻¹ * ‖cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ))‖) *
          ‖tau q (lift z q)⁻¹‖) * ‖tau q (lift w q)⁻¹‖
        ≤ (((((Nat.totient q : ℝ)) ^ 2)⁻¹ *
            (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ))) *
              Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) *
            Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
          refine mul_le_mul ?_ ht2 (norm_nonneg _) (by positivity)
          refine mul_le_mul ?_ ht1 (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left h1 hφnn
      _ = (((Nat.totient q : ℝ)) ^ 2)⁻¹ *
            ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ)) := by ring
  have hstep2 : ‖cCoefPrime z w q m‖ ≤
      ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) *
        ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) := by
    refine le_trans hprod ?_
    calc (((Nat.totient q : ℝ)) ^ 2)⁻¹ *
          ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ))
        ≤ ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) *
            ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hφbound (by positivity)
      _ = ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) *
            ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) := by ring
  have hinv_le : 1 / (q : ℝ) ^ 2 ≤ (q : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have h1 : (q : ℝ) ^ (-(2 : ℝ)) ≤ (q : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have h2 : (q : ℝ) ^ (-(2 : ℝ)) = 1 / (q : ℝ) ^ 2 := by
      rw [Real.rpow_neg hqR.le, Real.rpow_two, one_div]
    rwa [h2] at h1
  have hsplit : ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) *
        ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2))
      = (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
          (Real.log 2) ^ 2) * (1 / (q : ℝ) ^ 2) * (1 + Real.log (q : ℝ)) ^ 2 := by
    field_simp
  refine le_trans hstep2 ?_
  rw [hsplit]
  have h2' : (0 : ℝ) ≤ ((∑ e ∈ m.divisors, (e : ℝ)) *
      (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) / (Real.log 2) ^ 2 := by
    have := Real.sqrt_nonneg ((Nat.lcm z.r w.r : ℕ) : ℝ)
    positivity
  have h3' : (0 : ℝ) ≤ (1 + Real.log (q : ℝ)) ^ 2 := sq_nonneg _
  calc (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
        (Real.log 2) ^ 2) * (1 / (q : ℝ) ^ 2) * (1 + Real.log (q : ℝ)) ^ 2
      ≤ (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
          (Real.log 2) ^ 2) * (q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv_le h2') h3'
    _ = (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
          (Real.log 2) ^ 2) * ((q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2) := by
        ring


/-- Partial sums over `[1, Q]` converge for a summable sequence, with the `q = 0` term removed. -/
private theorem tendsto_Icc_sum_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun Q : ℕ => ∑ q ∈ Finset.Icc 1 Q, f q) atTop (𝓝 ((∑' q, f q) - f 0)) := by
  have h1 : ∀ Q : ℕ, ∑ q ∈ Finset.Icc 1 Q, f q = (∑ q ∈ Finset.range (Q + 1), f q) - f 0 := by
    intro Q
    have hset : Finset.range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    ring
  have h2 : Tendsto (fun Q : ℕ => ∑ q ∈ Finset.range (Q + 1), f q) atTop (𝓝 (∑' q, f q)) :=
    hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [h1] using h2.sub_const (f 0)

/-- **The masked coefficient series is summable.** -/
private theorem summable_masked_cCoefPrime (z w : ExcPair) (hz : z.χ.IsPrimitive)
    (hw : w.χ.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    Summable (fun q : ℕ => if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) := by
  set A : ℝ := (∑ e ∈ m.divisors, (e : ℝ)) *
    (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 / (Real.log 2) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    have := Real.sqrt_nonneg ((Nat.lcm z.r w.r : ℕ) : ℝ)
    positivity
  have hmaj : Summable (fun q : ℕ => A *
      (((q + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (((q + 1 : ℕ)) : ℝ)) ^ 2)) := by
    have hbase := summable_nat_rpow_mul_one_add_log_sq.mul_left A
    have hshift := (summable_nat_add_iff 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_norm_bounded (g := fun q : ℕ => A *
    (((q + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (((q + 1 : ℕ)) : ℝ)) ^ 2)) hmaj ?_
  intro q
  by_cases hd : Nat.lcm z.r w.r ∣ q + 1
  · rw [ite_eq_left hd]
    have hb := norm_cCoefPrime_le_gen z w hz hw m hm (q + 1) (Nat.le_add_left 1 q) hd
    rw [hA]
    simpa only [Nat.cast_add, Nat.cast_one] using hb
  · rw [ite_eq_right hd, norm_zero]
    exact mul_nonneg hA0 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))

/-- Every point of the exceptional set carries a primitive character. -/
private theorem isPrimitive_of_mem_excSet {H U P X : ℝ} {z : ExcPair} (hz : z ∈ excSet H U P X) :
    z.χ.IsPrimitive := by
  rcases Set.mem_insert_iff.mp hz with h | h
  · subst h
    exact DirichletCharacter.isPrimitive_one_level_one
  · exact h.2.1

end


end Transfer

/-- LEAF arXiv:1804.05561v1 display 9.16: the singular series converges at every positive
frequency. DECISION 2026-10-31 architect PC 20261031T2333Z-383: `0 < m` added; the old form was
false at `m = 0`, LeafAudit168.prime_zero_no_limit. -/
theorem leaf_singular_series_converges (H X P : ℝ) :
  ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by
  refine ⟨fun z w m => (∑' q : ℕ, if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) -
    (if Nat.lcm z.r w.r ∣ 0 then cCoefPrime z w 0 m else 0), ?_⟩
  intro z hz w hw m hm
  have hf := summable_masked_cCoefPrime z w (isPrimitive_of_mem_excSet hz)
    (isPrimitive_of_mem_excSet hw) m hm
  have hconv := tendsto_Icc_sum_of_summable hf
  have hfun : singPartialPrime z w m = fun Q => ∑ q ∈ Finset.Icc 1 Q,
      if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0 := by
    funext Q
    rw [singPartialPrime, ← Finset.sum_filter]
  rw [hfun]
  exact hconv

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

