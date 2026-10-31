/-
Unit U-1536, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0026: J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I,
Acta Arith. 109.2 (2003), 169-194.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

File b, Sections 5 and 6 of the paper, pp. 177-184, with `g = 2`, rescaled from `[0, 2π]` to
`[0, 1]`: the moment recurrence for products `∏_{j<L} φ(2^j x)` of a cosine polynomial
`φ(y) = Σ_{j ≤ k} b_j cos(2π j y)`, and an explicit certificate bounding `E_L(1)`.

* `vcoef k b n L = ∫_0^1 cos(2π n x) ∏_{j<L} φ(2^j x) dx`, the `v_{n,L}` of p. 177, case (a).
* `Umat k b`, the `k × k` matrix of Lemma 6, p. 179, `m = k - 1`, with entries
  `u_{nl} = ½ (b_{2l-n} + b_{2l+n} + b_{n-2l})` for `l ≥ 1` and `u_{n0} = ½ (b_{-n} + b_n)`.
  QUESTION, not a finding: the printed formula of Lemma 6 also adds `b_{n-gl}` at `l = 0`, which
  counts the term `j = n` of Lemma 5 twice; with it, `v_{0,1}` would be `3 b_0 / 2` instead of
  `b_0`.  The corrected matrix reproduces the direct integral numerically, see PROGRESS.md.
* The certificate: degree `k = 6`, `λ = 1`, `φ = b6` the degree 6 Taylor polynomial of `e^t` at
  `t = cos 2πy` plus `2.719/7!`, Perron vector `w6`, `ρ = 1.454`.  The paper uses the extremal
  polynomials of Theorem 3, degree 19; a cruder certificate suffices for `d = 3/4`.

Assemblies, CONDITIONAL ON the leaves: `lemma5`, `lemma7`, `up_b6`, `EL_one_le`.
Proved outright: `bz_nonneg`, `Umat_nonneg`, `b6_nonneg`, `w6_pos`.
-/
/- CODEX task180 closed every original leaf and added finite sum helpers.
The historical CONDITIONAL comments below describe the original dependency graph.
The current assemblies have no cited input and no sorry dependency.
AI wrote the new Lean code. Goldbach is open. -/
import Mathlib
import LeanLab.Linnik.Decomp1536a

namespace LeanLab.Linnik.Decomp1536b

open Real MeasureTheory Finset
open LeanLab.Linnik.Decomp1536a (Spow EL)
open scoped Matrix

/-- `φ(y) = Σ_{j=0}^{k} b_j cos(2π j y)`, (5.1), p. 177, rescaled to period 1. -/
noncomputable def cosPoly (k : ℕ) (b : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), b j * Real.cos (2 * π * ((j : ℝ) * y))

/-- `∏_{j=0}^{L-1} φ(2^j x)`, p. 177. -/
noncomputable def Fprod (k : ℕ) (b : ℕ → ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ range L, cosPoly k b ((2 : ℝ) ^ j * x)

/-- `v_{n,L} = ∫_0^1 cos(2π n x) ∏_{j<L} φ(2^j x) dx`, p. 177, Lebesgue case (a). -/
noncomputable def vcoef (k : ℕ) (b : ℕ → ℝ) (n L : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.cos (2 * π * ((n : ℝ) * x)) * Fprod k b L x

/-- `b_j` extended by `0` outside `0 ≤ j ≤ k`, Lemma 6, p. 179. -/
noncomputable def bz (k : ℕ) (b : ℕ → ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ k then b j.toNat else 0

/-- The matrix `U` of Lemma 6, p. 179, `g = 2`, `m = k - 1`, with the `l = 0` column corrected,
see the file header. -/
noncomputable def Umat (k : ℕ) (b : ℕ → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun n l => (1 / 2) * (bz k b (2 * ((l : ℕ) : ℤ) - ((n : ℕ) : ℤ)) +
    bz k b (2 * ((l : ℕ) : ℤ) + ((n : ℕ) : ℤ)) +
    if (l : ℕ) = 0 then 0 else bz k b (((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ)))

/-- The halving term of Lemma 5, p. 177: `V(|r|/2)` when `2 ∣ r`, else `0`. -/
noncomputable def hterm (V : ℕ → ℝ) (r : ℤ) : ℝ :=
  if 2 ∣ r then V (r.natAbs / 2) else 0

/-- LEAF. Unit U-1536. `∏_{j<L+1} φ(2^j x) = φ(x) ∏_{j<L} φ(2^j (2x))`, first line of the proof of
Lemma 5, p. 178. -/
theorem Fprod_succ (k : ℕ) (b : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    Fprod k b (L + 1) x = cosPoly k b x * Fprod k b L (2 * x) := by
  unfold Fprod
  rw [Finset.prod_range_succ', mul_comm]
  simp only [pow_zero, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_succ]
  congr 1
  ring

/-- LEAF. Unit U-1536. The product has period 1, p. 178, "the product has period 2π/g", rescaled. -/
theorem Fprod_periodic (k : ℕ) (b : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    Fprod k b L (x + 1) = Fprod k b L x := by
  unfold Fprod
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold cosPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * π * ((j : ℝ) * ((2 : ℝ) ^ a * (x + 1))) =
    2 * π * ((j : ℝ) * ((2 : ℝ) ^ a * x)) + (j * 2 ^ a : ℕ) * (2 * π) by
      push_cast
      ring]
  rw [Real.cos_add_nat_mul_two_pi]

/-- LEAF. Unit U-1536. The product is continuous. -/
theorem Fprod_continuous (k : ℕ) (b : ℕ → ℝ) (L : ℕ) : Continuous (Fprod k b L) := by
  unfold Fprod
  apply continuous_finsetProd
  intro j _
  unfold cosPoly
  apply continuous_finsetSum
  intro m _
  fun_prop

/-- LEAF. Unit U-1536. Product to sum, the expansion of `h(x) = φ(x) cos nx` in the proof of
Lemma 5, p. 178: `cos(2πnx) φ(x) = ½ Σ_j b_j (cos(2π(j+n)x) + cos(2π(j-n)x))`. -/
theorem cos_mul_cosPoly (k : ℕ) (b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    Real.cos (2 * π * ((n : ℝ) * x)) * cosPoly k b x =
      (1 / 2) * ∑ j ∈ range (k + 1), b j *
        (Real.cos (2 * π * ((((j : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) +
          Real.cos (2 * π * ((((j : ℤ) - (n : ℤ) : ℤ) : ℝ) * x))) := by
  unfold cosPoly
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [show 2 * π * (((j : ℝ) + n) * x) = 2 * π * ((j : ℝ) * x) + 2 * π * ((n : ℝ) * x) by ring,
    show 2 * π * (((j : ℝ) - n) * x) = 2 * π * ((j : ℝ) * x) - 2 * π * ((n : ℝ) * x) by ring,
    add_comm (Real.cos _) (Real.cos _), ← Real.two_mul_cos_mul_cos]
  ring

/-- LEAF. Unit U-1536. The halving step of Lemma 5, p. 178, the averaging over `ν` and the change of
variable `x → x/g`, `g = 2`: for continuous `F` of period 1 and integer `r`,
`∫_0^1 cos(2π r x) F(2x) dx` is `∫_0^1 cos(2π (|r|/2) y) F(y) dy` if `2 ∣ r` and `0` otherwise. -/
theorem halving {F : ℝ → ℝ} (hF : Continuous F) (hper : ∀ x, F (x + 1) = F x) (r : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * ((r : ℝ) * x)) * F (2 * x) =
      hterm (fun m => ∫ y in (0 : ℝ)..1, Real.cos (2 * π * ((m : ℝ) * y)) * F y) r := by
  unfold hterm
  split_ifs with hd
  · obtain ⟨q, hq⟩ := hd
    have hm : r.natAbs / 2 = q.natAbs := by rw [hq, Int.natAbs_mul]; simp
    rw [hm]
    let G : ℝ → ℝ := fun y => Real.cos (2 * π * ((q.natAbs : ℝ) * y)) * F y
    have hG : Continuous G := (Real.continuous_cos.comp (by fun_prop)).mul hF
    have hp : Function.Periodic G 1 := by
      intro y
      dsimp [G]
      rw [show 2 * π * ((q.natAbs : ℝ) * (y + 1)) =
        2 * π * ((q.natAbs : ℝ) * y) + q.natAbs * (2 * π) by ring,
        Real.cos_add_nat_mul_two_pi, hper]
    have hcos (y : ℝ) : Real.cos (2 * π * ((q : ℝ) * y)) =
        Real.cos (2 * π * ((q.natAbs : ℝ) * y)) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      by_cases hq0 : (0 : ℝ) ≤ q
      · rw [abs_of_nonneg hq0]
      · rw [abs_of_neg (lt_of_not_ge hq0),
          show 2 * π * (-(q : ℝ) * y) = -(2 * π * ((q : ℝ) * y)) by ring, Real.cos_neg]
    have he : ∀ x : ℝ, Real.cos (2 * π * ((r : ℝ) * x)) * F (2 * x) = G (2 * x) := by
      intro x
      dsimp [G]
      rw [← hcos, hq]
      push_cast
      congr 2
      ring
    rw [intervalIntegral.integral_congr (fun x _ => he x)]
    change (∫ x in (0 : ℝ)..1, G (2 * x)) = ∫ y in (0 : ℝ)..1, G y
    rw [intervalIntegral.integral_comp_mul_left G two_ne_zero]
    have hs := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) 0 (fun a b => hG.intervalIntegrable a b)
    norm_num [smul_eq_mul] at hs ⊢
    rw [hs]
    ring
  · have ho : Odd r := Int.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hd)
    let G : ℝ → ℝ := fun x => Real.cos (2 * π * ((r : ℝ) * x)) * F (2 * x)
    have hp : Function.Periodic G 1 := by
      intro x
      dsimp [G]
      rw [show 2 * π * ((r : ℝ) * (x + 1)) =
        2 * π * ((r : ℝ) * x) + r * (2 * π) by ring,
        Real.cos_add_int_mul_two_pi,
        show 2 * (x + 1) = (2 * x + 1) + 1 by ring, hper, hper]
    have ha : ∀ x : ℝ, G (x + 1 / 2) = -G x := by
      intro x
      dsimp [G]
      rw [show 2 * π * ((r : ℝ) * (x + 1 / 2)) =
        2 * π * ((r : ℝ) * x) + r * π by ring,
        Real.cos_add_int_mul_pi, ho.neg_one_zpow,
        show 2 * (x + 1 / 2) = 2 * x + 1 by ring, hper]
      ring
    have hs := hp.intervalIntegral_add_eq (1 / 2) 0
    have ht := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1) G (1 / 2)
    have hn : (∫ x in (0 : ℝ)..1, G (x + 1 / 2)) = -(∫ x in (0 : ℝ)..1, G x) := by
      simp_rw [ha]
      exact intervalIntegral.integral_neg
    change (∫ x in (0 : ℝ)..1, G x) = 0
    norm_num only [zero_add, add_comm (1 : ℝ)] at hs ht
    linarith

/-- LEAF. Unit U-1536. Initial values, p. 179, continuous case: `v_{0,0} = 1`, `v_{n,0} = 0` for
`n ≥ 1`. -/
theorem vcoef_zero (k : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    vcoef k b n 0 = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [vcoef, Fprod, hn]
  · simp only [vcoef, Fprod, Finset.range_zero, Finset.prod_empty, mul_one, ite_eq_right hn]
    have hc : 2 * π * (n : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Nat.cast_ne_zero.mpr hn)
    simp_rw [show ∀ x : ℝ, 2 * π * ((n : ℝ) * x) = (2 * π * n) * x by intro x; ring]
    rw [intervalIntegral.integral_comp_mul_left _ hc]
    simp only [mul_zero, mul_one, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul]
    rw [show 2 * π * (n : ℝ) = (2 * n : ℕ) * π by push_cast; ring, Real.sin_nat_mul_pi]
    simp

/-- The signed frequency expansion behind Lemma 6, p.179. The zero frequency is counted once. -/
theorem hterm_eq_signed_sum (k : ℕ) (V : ℕ → ℝ) (r : ℤ) (hr : r.natAbs < 2 * k) :
    hterm V r = ∑ l : Fin k,
      ((if r = 2 * ((l : ℕ) : ℤ) then V l else 0) +
       (if (l : ℕ) ≠ 0 ∧ r = -2 * ((l : ℕ) : ℤ) then V l else 0)) := by
  classical
  unfold hterm
  split_ifs with hd
  · have hdiv : 2 ∣ r.natAbs := Int.natCast_dvd.mp hd
    have hm2 : 2 * (r.natAbs / 2) = r.natAbs := Nat.mul_div_cancel' hdiv
    let m : Fin k := ⟨r.natAbs / 2, by omega⟩
    rw [Finset.sum_eq_single m]
    · have ha := Int.natAbs_eq r
      rcases ha with ha | ha
      · have he : r = 2 * ((m : ℕ) : ℤ) := by dsimp [m]; omega
        have hn : ¬((m : ℕ) ≠ 0 ∧ r = -2 * ((m : ℕ) : ℤ)) := by omega
        simp only [ite_eq_left he, ite_eq_right hn, add_zero]
        rfl
      · have he : r = -2 * ((m : ℕ) : ℤ) := by dsimp [m]; omega
        by_cases hm0 : (m : ℕ) = 0
        · have hz : r = 0 := by omega
          simp [hz, m] at *
        · have hn : r ≠ 2 * ((m : ℕ) : ℤ) := by omega
          simp only [ite_eq_right hn, ite_eq_left (And.intro hm0 he), zero_add]
          rfl
    · intro l _ hl
      have hne : (l : ℕ) ≠ (m : ℕ) := fun he => hl (Fin.ext he)
      have hn1 : r ≠ 2 * ((l : ℕ) : ℤ) := by
        intro he
        have ha := Int.natAbs_eq r
        rcases ha with ha | ha <;> dsimp [m] at hne <;> omega
      have hn2 : ¬((l : ℕ) ≠ 0 ∧ r = -2 * ((l : ℕ) : ℤ)) := by
        rintro ⟨_, he⟩
        have ha := Int.natAbs_eq r
        rcases ha with ha | ha <;> dsimp [m] at hne <;> omega
      simp only [ite_eq_right hn1, ite_eq_right hn2, zero_add]
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro l _
    have h1 : r ≠ 2 * ((l : ℕ) : ℤ) := by rintro rfl; exact hd (dvd_mul_right 2 _)
    have h2 : ¬((l : ℕ) ≠ 0 ∧ r = -2 * ((l : ℕ) : ℤ)) := by
      rintro ⟨_, rfl⟩
      apply hd
      exact ⟨-((l : ℕ) : ℤ), by ring⟩
    simp only [ite_eq_right h1, ite_eq_right h2, zero_add]

/-- A single supported coefficient in the finite sum of Lemma 6, p.179. -/
theorem sum_bz_ite (k : ℕ) (b : ℕ → ℝ) (r : ℤ) (c : ℝ) :
    ∑ j ∈ range (k + 1), b j * (if (j : ℤ) = r then c else 0) = bz k b r * c := by
  classical
  by_cases hr : 0 ≤ r ∧ r ≤ k
  · have hm : r.toNat ∈ range (k + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single_of_mem r.toNat hm]
    · simp [bz, hr, show (r.toNat : ℤ) = r by omega]
    · intro j hj hjn
      have hn : (j : ℤ) ≠ r := by omega
      simp only [ite_eq_right hn, mul_zero]
  · rw [bz, ite_eq_right hr, zero_mul]
    apply Finset.sum_eq_zero
    intro j hj
    have hn : (j : ℤ) ≠ r := by have hj' := Finset.mem_range.mp hj; omega
    simp only [ite_eq_right hn, mul_zero]

/-- LEAF. Unit U-1536. The index restriction behind Lemma 6, p. 179, `g = 2`, `m = k - 1`:
for `n ≤ k - 1` the right side of Lemma 5 involves only `V l` with `l ≤ k - 1`, and equals
`Σ_l u_{nl} V l` with the matrix `Umat`.  Pure finite algebra. -/
theorem lemma6_reindex {k : ℕ} (hk : 1 ≤ k) (b : ℕ → ℝ) (V : ℕ → ℝ) (n : Fin k) :
    (1 / 2) * ∑ j ∈ range (k + 1), b j *
        (hterm V ((j : ℤ) + ((n : ℕ) : ℤ)) + hterm V ((j : ℤ) - ((n : ℕ) : ℤ))) =
      ∑ l : Fin k, Umat k b n l * V l := by
  classical
  have hn := n.isLt
  have _hk := hk
  have htermj (j : ℕ) (hj : j ∈ range (k + 1)) :
      hterm V ((j : ℤ) + ((n : ℕ) : ℤ)) + hterm V ((j : ℤ) - ((n : ℕ) : ℤ)) =
        ∑ l : Fin k,
          ((if (j : ℤ) = 2 * ((l : ℕ) : ℤ) - ((n : ℕ) : ℤ) then V l else 0) +
           (if (j : ℤ) = 2 * ((l : ℕ) : ℤ) + ((n : ℕ) : ℤ) then V l else 0) +
           (if (l : ℕ) ≠ 0 ∧ (j : ℤ) = ((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ) then V l else 0)) := by
    have hj' := Finset.mem_range.mp hj
    have hplus : ((j : ℤ) + ((n : ℕ) : ℤ)).natAbs < 2 * k := by
      rcases Int.natAbs_eq ((j : ℤ) + ((n : ℕ) : ℤ)) with h | h <;> omega
    have hminus : ((j : ℤ) - ((n : ℕ) : ℤ)).natAbs < 2 * k := by
      rcases Int.natAbs_eq ((j : ℤ) - ((n : ℕ) : ℤ)) with h | h <;> omega
    rw [hterm_eq_signed_sum k V _ hplus, hterm_eq_signed_sum k V _ hminus,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hp : ((j : ℤ) + ((n : ℕ) : ℤ) = 2 * ((l : ℕ) : ℤ)) ↔
        (j : ℤ) = 2 * ((l : ℕ) : ℤ) - ((n : ℕ) : ℤ) := by omega
    have hm : ((j : ℤ) - ((n : ℕ) : ℤ) = 2 * ((l : ℕ) : ℤ)) ↔
        (j : ℤ) = 2 * ((l : ℕ) : ℤ) + ((n : ℕ) : ℤ) := by omega
    have hneg : ¬((l : ℕ) ≠ 0 ∧ (j : ℤ) + ((n : ℕ) : ℤ) = -2 * ((l : ℕ) : ℤ)) := by omega
    have hneg' : ((j : ℤ) - ((n : ℕ) : ℤ) = -2 * ((l : ℕ) : ℤ)) ↔
        (j : ℤ) = ((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ) := by omega
    simp only [ite_eq_right hneg, add_zero, hp, hm, hneg']
    ring
  have hrow := Finset.sum_congr rfl (fun j hj => congrArg (fun z : ℝ => b j * z) (htermj j hj))
  rw [hrow]
  calc
    _ = ∑ l : Fin k, (1 / 2 : ℝ) * ∑ j ∈ range (k + 1), b j *
          ((if (j : ℤ) = 2 * ((l : ℕ) : ℤ) - ((n : ℕ) : ℤ) then V l else 0) +
           (if (j : ℤ) = 2 * ((l : ℕ) : ℤ) + ((n : ℕ) : ℤ) then V l else 0) +
           (if (l : ℕ) ≠ 0 ∧ (j : ℤ) = ((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ) then V l else 0)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      refine Finset.sum_congr rfl fun l _ => ?_
      have ht : (∑ j ∈ range (k + 1), b j *
          (if (l : ℕ) ≠ 0 ∧ (j : ℤ) = ((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ) then V l else 0)) =
          (if (l : ℕ) = 0 then 0 else bz k b (((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ))) * V l := by
        by_cases hl : (l : ℕ) = 0
        · simp only [hl, ne_eq, not_true_eq_false, false_and, ite_false, mul_zero, Finset.sum_const_zero, ite_true, zero_mul]
        · simp only [hl, ne_eq, not_false_eq_true, true_and, ite_false]
          exact sum_bz_ite k b _ _
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [sum_bz_ite, sum_bz_ite, ht]
      unfold Umat
      split_ifs <;> ring

/-- p.179 paragraph after Lemma 7. Auxiliary weighted power bound. -/
theorem perron_mulVec_le {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : ∀ i j, 0 ≤ U i j)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (ρ : ℝ) (h : ∀ i, (U *ᵥ w) i ≤ ρ * w i)
    (L : ℕ) (i : Fin k) : ((U ^ L) *ᵥ w) i ≤ ρ ^ L * w i := by
  have hr : 0 ≤ ρ := by
    have hn : 0 ≤ (U *ᵥ w) i := by
      change 0 ≤ ∑ j, U i j * w j
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hU i j) (hw j).le
    nlinarith [h i, hw i]
  induction L generalizing i with
  | zero => simp
  | succ L ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc
      (U *ᵥ ((U ^ L) *ᵥ w)) i ≤ ∑ j, U i j * (ρ ^ L * w j) := by
        change (∑ j, U i j * ((U ^ L) *ᵥ w) j) ≤ _
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hU i j)
      _ = ρ ^ L * (U *ᵥ w) i := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ρ ^ L * (ρ * w i) := mul_le_mul_of_nonneg_left (h i) (pow_nonneg hr L)
      _ = ρ ^ (L + 1) * w i := by rw [pow_succ]; ring

/-- p.179 paragraph after Lemma 7. Auxiliary weighted entry bound. -/
theorem perron_entry_mul_le {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : ∀ i j, 0 ≤ U i j)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (ρ : ℝ) (h : ∀ i, (U *ᵥ w) i ≤ ρ * w i)
    (L : ℕ) (i j : Fin k) : (U ^ L) i j * w j ≤ ρ ^ L * w i := by
  calc
    _ ≤ ((U ^ L) *ᵥ w) i := by
      exact Finset.single_le_sum (fun a _ => mul_nonneg (Matrix.pow_apply_nonneg hU L i a) (hw a).le)
        (Finset.mem_univ j)
    _ ≤ _ := perron_mulVec_le U hU w hw ρ h L i

/-- LEAF. Unit U-1536. Perron bound, used after Lemma 7, p. 179, "the asymptotic behaviour depends
on the largest eigenvalue of U": if `U ≥ 0` entrywise, `w > 0` and `U w ≤ ρ w` entrywise, then
`(U^L)_{ii} ≤ ρ^L`. -/
theorem perron {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : ∀ i j, 0 ≤ U i j)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (ρ : ℝ) (h : ∀ i, (U *ᵥ w) i ≤ ρ * w i)
    (L : ℕ) (i : Fin k) : (U ^ L) i i ≤ ρ ^ L := by
  have he := perron_entry_mul_le U hU w hw ρ h L i i
  nlinarith [hw i]

/-- LEAF. Unit U-1536. Comparison, (5.2), p. 177: if `e^{λ cos 2πy} ≤ φ(y)` for all `y`, then
`E_L(λ) = ∫_0^1 ∏_j e^{λ cos(2π 2^j x)} ≤ ∫_0^1 ∏_j φ(2^j x) = v_{0,L}`. -/
theorem EL_le_vcoef {k : ℕ} {b : ℕ → ℝ} {lam : ℝ}
    (hup : ∀ y, Real.exp (lam * Real.cos (2 * π * y)) ≤ cosPoly k b y) (L : ℕ) :
    EL L lam ≤ vcoef k b 0 L := by
  unfold EL vcoef
  simp only [Nat.cast_zero, zero_mul, mul_zero, Real.cos_zero, one_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((Real.continuous_exp.comp
      (continuous_const.mul (LeanLab.Linnik.Decomp1536a.continuous_SL L))).intervalIntegrable 0 1)
    ((Fprod_continuous k b L).intervalIntegrable 0 1)
  intro x _
  change Real.exp (lam * ∑ j ∈ range L, Real.cos (2 * π * ((2 : ℝ) ^ j * x))) ≤ _
  unfold Fprod
  rw [Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le) (fun j _ => hup _)

/-! ### Assemblies for Lemmas 5 and 7 -/

/-- Lemma 5, p. 177, `g = 2`, continuous case:
`v_{n,L+1} = ½ Σ_j b_j (v_{(j+n)/2, L} [2 ∣ j+n] + v_{|j-n|/2, L} [2 ∣ j-n])`.
CONDITIONAL ON `Fprod_succ`, `Fprod_periodic`, `Fprod_continuous`, `cos_mul_cosPoly`, `halving`. -/
theorem lemma5 (k : ℕ) (b : ℕ → ℝ) (n L : ℕ) :
    vcoef k b n (L + 1) = (1 / 2) * ∑ j ∈ range (k + 1), b j *
      (hterm (fun m => vcoef k b m L) ((j : ℤ) + (n : ℤ)) +
        hterm (fun m => vcoef k b m L) ((j : ℤ) - (n : ℤ))) := by
  have hF := Fprod_continuous k b L
  have hP := Fprod_periodic k b L
  have hc : ∀ r : ℤ, Continuous fun x : ℝ =>
      Real.cos (2 * π * ((r : ℝ) * x)) * Fprod k b L (2 * x) := by
    intro r
    exact (Real.continuous_cos.comp (by fun_prop)).mul (hF.comp (by fun_prop))
  have hpt : ∀ x : ℝ, Real.cos (2 * π * ((n : ℝ) * x)) * Fprod k b (L + 1) x =
      ∑ j ∈ range (k + 1),
        ((1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x)) +
          (1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) - (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x))) := by
    intro x
    rw [Fprod_succ, ← mul_assoc, cos_mul_cosPoly, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : vcoef k b n (L + 1) = ∫ x in (0 : ℝ)..1, ∑ j ∈ range (k + 1),
        ((1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x)) +
          (1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) - (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x))) := by
    unfold vcoef
    exact intervalIntegral.integral_congr fun x _ => hpt x
  rw [hL, intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_add (((hc _).intervalIntegrable 0 1).const_mul _)
        (((hc _).intervalIntegrable 0 1).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      halving hF hP, halving hF hP]
    unfold vcoef
    ring
  · intro j _
    exact (((hc _).intervalIntegrable 0 1).const_mul _).add
      (((hc _).intervalIntegrable 0 1).const_mul _)

/-- The vector form of Lemmas 6 and 7: `(v_{0,L}, ..., v_{k-1,L}) = U^L e_0`.
CONDITIONAL ON `lemma5`'s leaves, `vcoef_zero`, `lemma6_reindex`. -/
theorem vvec_eq {k : ℕ} (hk : 1 ≤ k) (b : ℕ → ℝ) (L : ℕ) :
    (fun n : Fin k => vcoef k b n L) = (Umat k b ^ L) *ᵥ (Pi.single ⟨0, hk⟩ 1) := by
  induction L with
  | zero =>
    funext n
    rw [pow_zero, Matrix.one_mulVec, vcoef_zero, Pi.single_apply]
    simp [Fin.ext_iff]
  | succ L ih =>
    funext n
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, lemma5, lemma6_reindex hk]
    rfl

/-- Lemma 7, p. 179, continuous case: `∫_0^1 ∏_{j<L} φ(2^j x) dx = (U^L)_{00}`.
CONDITIONAL ON the leaves behind `vvec_eq`. -/
theorem lemma7 {k : ℕ} (hk : 1 ≤ k) (b : ℕ → ℝ) (L : ℕ) :
    vcoef k b 0 L = (Umat k b ^ L) ⟨0, hk⟩ ⟨0, hk⟩ := by
  have := congrFun (vvec_eq hk b L) ⟨0, hk⟩
  simp only at this
  rw [this]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `b_j ≥ 0` gives `bz ≥ 0`. Proved. -/
theorem bz_nonneg {k : ℕ} {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (j : ℤ) : 0 ≤ bz k b j := by
  unfold bz
  split_ifs
  · exact hb _
  · exact le_refl 0

/-- `b_j ≥ 0` gives `U ≥ 0` entrywise, as needed for `perron`. Proved. -/
theorem Umat_nonneg {k : ℕ} {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (n l : Fin k) :
    0 ≤ Umat k b n l := by
  unfold Umat
  have h1 := bz_nonneg (k := k) hb (2 * ((l : ℕ) : ℤ) - ((n : ℕ) : ℤ))
  have h2 := bz_nonneg (k := k) hb (2 * ((l : ℕ) : ℤ) + ((n : ℕ) : ℤ))
  have h3 := bz_nonneg (k := k) hb (((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ))
  split_ifs <;> positivity

/-! ### The explicit certificate, `k = 6`, `λ = 1` -/

/-- Cosine coefficients of `Σ_{n ≤ 6} cos(2πy)^n / n! + 2719/5040000`; the constant
`2719/5040000 = 2.719/7!` bounds the Taylor remainder `e/7!`. -/
noncomputable def b6 : ℕ → ℝ
  | 0 => 4255771 / 3360000
  | 1 => 217 / 192
  | 2 => 139 / 512
  | 3 => 17 / 384
  | 4 => 7 / 1280
  | 5 => 1 / 1920
  | 6 => 1 / 23040
  | _ => 0

/-- The Perron vector, rounded. -/
noncomputable def w6 : Fin 6 → ℝ := ![1, 3361 / 5000, 7519 / 10000, 5781 / 10000, 1551 / 2000, 1079 / 2000]

/-- Proved. -/
theorem b6_nonneg (j : ℕ) : 0 ≤ b6 j := by
  unfold b6
  split <;> norm_num

/-- Proved. -/
theorem w6_pos (i : Fin 6) : 0 < w6 i := by
  fin_cases i <;> simp [w6]

/-- LEAF. Unit U-1536. The cosine expansion of the upper polynomial, Section 6, p. 180, "a cosine
polynomial can be written as `φ(x) = f(cos x)`": with `t = cos 2πy`,
`Σ_{j ≤ 6} b6_j cos(2π j y) = Σ_{n ≤ 6} t^n/n! + 2719/5040000`.  Multiple angle identities. -/
theorem cosPoly_b6 (y : ℝ) :
    cosPoly 6 b6 y =
      ∑ n ∈ range 7, Real.cos (2 * π * y) ^ n / (n.factorial : ℝ) + 2719 / 5040000 := by
  have hc (j : ℕ) : Real.cos (2 * π * ((j : ℝ) * y)) =
      (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (Real.cos (2 * π * y)) := by
    rw [Polynomial.Chebyshev.T_real_cos]
    congr 1
    push_cast
    ring
  have h3 := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ)
  have h4 := Polynomial.Chebyshev.T_add_two ℝ (2 : ℤ)
  have h5 := Polynomial.Chebyshev.T_add_two ℝ (3 : ℤ)
  have h6 := Polynomial.Chebyshev.T_add_two ℝ (4 : ℤ)
  norm_num only at h3 h4 h5 h6
  unfold cosPoly
  simp_rw [hc]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, b6, h6, h5, h4, h3,
    Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one, Polynomial.Chebyshev.T_zero,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_pow, Nat.factorial]
  ring

/-- LEAF. Unit U-1536. An upper approximation as in (6.2), p. 180, `λ = 1`, degree 6:
for `|t| ≤ 1`, `e^t ≤ Σ_{n ≤ 6} t^n/n! + 2719/5040000`; the Taylor remainder is at most
`e/7! < 2.719/5040`. -/
theorem exp_le_taylor6 {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    Real.exp t ≤ ∑ n ∈ range 7, t ^ n / (n.factorial : ℝ) + 2719 / 5040000 := by
  have ha : |t| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have h := (abs_le.mp (Real.exp_bound (n := 7) ha (by norm_num))).2
  have hp : |t| ^ 7 ≤ 1 := pow_le_one₀ (abs_nonneg t) ha
  have hc : ((Nat.succ 7 : ℕ) : ℝ) / (((7 : ℕ).factorial : ℝ) * ((7 : ℕ) : ℝ)) =
      (8 / 35280 : ℝ) := by norm_num
  rw [hc] at h
  have hb := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ 8 / 35280 by norm_num)
  linarith

/-- LEAF. Unit U-1536. The Perron certificate for the matrix of Lemma 6 built from `b6`:
`(U w6)_i ≤ 1.454 (w6)_i` for every `i`, exact rational arithmetic; the margins are between
`3.9·10⁻⁴` and `7.8·10⁻⁴`, numerics/u1536_cert.py.  The spectral radius is about `1.45322`. -/
theorem cert6 (i : Fin 6) : (Umat 6 b6 *ᵥ w6) i ≤ 1454 / 1000 * w6 i := by
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Umat, bz, b6, w6]

/-- `e^{cos 2πy} ≤ φ(y)` for `φ = b6`, the upper approximation of (5.2) with `λ = 1`.
CONDITIONAL ON `cosPoly_b6`, `exp_le_taylor6`. -/
theorem up_b6 (y : ℝ) : Real.exp (1 * Real.cos (2 * π * y)) ≤ cosPoly 6 b6 y := by
  rw [one_mul, cosPoly_b6]
  exact exp_le_taylor6 (Real.neg_one_le_cos _) (Real.cos_le_one _)

/-- `E_L(1) ≤ 1.454^L`, so `ψ(1) ≤ log 1.454 < 0.3744`, the numerical input of Section 7, p. 184,
from Sections 5 and 6.  CONDITIONAL ON the leaves of this file. -/
theorem EL_one_le (L : ℕ) : EL L 1 ≤ (1454 / 1000 : ℝ) ^ L := by
  have hk : 1 ≤ 6 := by norm_num
  calc EL L 1 ≤ vcoef 6 b6 0 L := EL_le_vcoef up_b6 L
    _ = (Umat 6 b6 ^ L) ⟨0, hk⟩ ⟨0, hk⟩ := lemma7 hk b6 L
    _ ≤ (1454 / 1000 : ℝ) ^ L :=
        perron _ (Umat_nonneg b6_nonneg) w6 w6_pos _ cert6 L _

/-! Further consequences of the Section 5 recurrence and the Section 7 certificate. -/

open Filter
open scoped Topology
open LeanLab.Linnik.Decomp1536a (EL_pos EL_rate_exists one_le_EL)

/-- pp.177 and 178 Lemma 5. Auxiliary positivity consequence. -/
theorem vcoef_nonneg {k : ℕ} {b : ℕ → ℝ} (hb : ∀ j ≤ k, 0 ≤ b j) (n L : ℕ) : 0 ≤ vcoef k b n L := by
  induction L generalizing n with
  | zero => rw [vcoef_zero]; split_ifs <;> norm_num
  | succ L ih =>
    rw [lemma5]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    have hh (r : ℤ) : 0 ≤ hterm (fun m => vcoef k b m L) r := by
      unfold hterm
      split_ifs
      · exact ih _
      · exact le_refl 0
    exact mul_nonneg (hb j (by have hj' := Finset.mem_range.mp hj; omega)) (add_nonneg (hh _) (hh _))

/-- p.177 product of cosine polynomials and pp.177 and 178 Lemma 5. Auxiliary exact degree support. -/
theorem vcoef_eq_zero_of_degree_lt {k : ℕ} {b : ℕ → ℝ} (n L : ℕ) (hn : k * (2 ^ L - 1) < n) : vcoef k b n L = 0 := by
  induction L generalizing n with
  | zero => simp only [pow_zero, Nat.sub_self, mul_zero] at hn; simp [vcoef_zero, Nat.ne_of_gt hn]
  | succ L ih =>
    have hpow : 2 ^ (L + 1) - 1 = 2 * (2 ^ L - 1) + 1 := by
      have hp : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by norm_num)
      rw [pow_succ]
      omega
    have hdeg : k * (2 ^ (L + 1) - 1) = 2 * (k * (2 ^ L - 1)) + k := by rw [hpow]; ring
    rw [hdeg] at hn
    have hh (r : ℤ) (hr : 2 * (k * (2 ^ L - 1)) < r.natAbs) :
        hterm (fun m => vcoef k b m L) r = 0 := by
      unfold hterm
      split_ifs with hd
      · have hdiv : 2 ∣ r.natAbs := Int.natCast_dvd.mp hd
        have he := Nat.mul_div_cancel' hdiv
        exact ih _ (by omega)
      · rfl
    rw [lemma5]
    have hz : ∑ j ∈ range (k + 1), b j *
        (hterm (fun m => vcoef k b m L) ((j : ℤ) + (n : ℤ)) +
         hterm (fun m => vcoef k b m L) ((j : ℤ) - (n : ℤ))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hp : 2 * (k * (2 ^ L - 1)) < ((j : ℤ) + (n : ℤ)).natAbs := by
        rcases Int.natAbs_eq ((j : ℤ) + (n : ℤ)) with ha | ha <;> omega
      have hm : 2 * (k * (2 ^ L - 1)) < ((j : ℤ) - (n : ℤ)).natAbs := by
        rcases Int.natAbs_eq ((j : ℤ) - (n : ℤ)) with ha | ha <;> omega
      rw [hh _ hp, hh _ hm]
      ring
    rw [hz, mul_zero]

/-- pp.177 and 178 Lemma 5. Auxiliary monotonicity consequence. -/
theorem vcoef_mono {k : ℕ} {b c : ℕ → ℝ} (hb : ∀ j ≤ k, 0 ≤ b j)
    (hbc : ∀ j ≤ k, b j ≤ c j) (n L : ℕ) : vcoef k b n L ≤ vcoef k c n L := by
  induction L generalizing n with
  | zero => rw [vcoef_zero, vcoef_zero]
  | succ L ih =>
    rw [lemma5, lemma5]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j ≤ k := by have hj' := Finset.mem_range.mp hj; omega
    have hh (r : ℤ) : hterm (fun m => vcoef k b m L) r ≤ hterm (fun m => vcoef k c m L) r := by
      unfold hterm
      split_ifs
      · exact ih _
      · exact le_refl 0
    have hh0 (r : ℤ) : 0 ≤ hterm (fun m => vcoef k b m L) r := by
      unfold hterm
      split_ifs
      · exact vcoef_nonneg hb _ L
      · exact le_refl 0
    exact mul_le_mul (hbc j hjk) (add_le_add (hh _) (hh _))
      (add_nonneg (hh0 _) (hh0 _)) ((hb j hjk).trans (hbc j hjk))

/-- p.179 vector recurrence and matrix method. Auxiliary degree six certificate envelope. -/
theorem vcoef_b6_bounds (L : ℕ) (n : Fin 6) :
    0 ≤ vcoef 6 b6 n L ∧ vcoef 6 b6 n L ≤ (1454 / 1000 : ℝ) ^ L * w6 n := by
  constructor
  · exact vcoef_nonneg (fun j _ => b6_nonneg j) n L
  · have hv := congrFun (vvec_eq (by norm_num : 1 ≤ 6) b6 L) n
    have he := perron_entry_mul_le (Umat 6 b6) (Umat_nonneg b6_nonneg) w6 w6_pos
      (1454 / 1000 : ℝ) cert6 L n ⟨0, by norm_num⟩
    have hw0 : w6 ⟨0, by norm_num⟩ = 1 := by norm_num [w6]
    rw [hw0, mul_one] at he
    have hv' : vcoef 6 b6 n L = (Umat 6 b6 ^ L) n ⟨0, by norm_num⟩ := by
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hv
    rw [hv']
    exact he

/-- pp.184 and 185 rate estimate method. Auxiliary degree six certificate arithmetic. -/
theorem log_cert6_lt : Real.log (1454 / 1000 : ℝ) < 3744 / 10000 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (x := (3744 / 10000 : ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- p.172 Theorem 2a and pp.184 and 185 upper rate estimate method. Auxiliary degree six certificate. -/
theorem EL_one_rate : ∃ psi : ℝ, 0 ≤ psi ∧ psi ≤ Real.log (1454 / 1000 : ℝ) ∧
    Tendsto (fun L : ℕ => Real.log (EL L 1) / (L : ℝ)) atTop (𝓝 psi) := by
  obtain ⟨psi, hpsi⟩ := EL_rate_exists 1
  refine ⟨psi, ?_, ?_, hpsi⟩
  · exact ge_of_tendsto' hpsi (fun L => div_nonneg (Real.log_nonneg (one_le_EL L zero_le_one)) (Nat.cast_nonneg L))
  · apply le_of_tendsto hpsi
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    rw [div_le_iff₀ hL0]
    have h := Real.log_le_log (EL_pos L 1) (EL_one_le L)
    rw [Real.log_pow] at h
    nlinarith

end LeanLab.Linnik.Decomp1536b
