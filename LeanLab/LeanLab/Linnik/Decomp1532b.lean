/-
Unit U-1532, run 20261026T0004Z-24325, DECOMPOSE.
Gallagher 1975, Primes and powers of 2, Invent. Math. 29, 125-142, base g = 2.

File b: the major arcs of Section 1, pp. 127-132, and Lemmas 6, 9, 10 of Section 2,
pp. 134-137.
* `majorArcs N P`: the union of the arcs `|α - a/q| ≤ 1/(qQ)`, `Q = N/P`, `1 ≤ q ≤ P`,
  `(a, q) = 1`, inside `[0, 1]`, display (2) p. 127. The arc of `a/q = 0/1` and `1/1` together
  are the arc `M(1, 1)` of the paper taken mod 1.
* `ramanujanSum q n = c_q(n)`, `singSeries n = Σ_q μ(q)²/φ(q)² c_q(n)`, p. 130 and p. 134.
* `Jn N n = Σ_{m₁ - m₂ = n} 1/(log m₁ log m₂)`, Theorem 3, p. 127.
* `zeroCount χ σ T`, the distinct zeros of `L(s, χ)` with `Re ρ ≥ σ`, `|Im ρ| ≤ T`.
* `excSet b T`, primitive characters of conductor at most `T` whose L-function has a zero with
  `Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`, p. 127.
Leaves: disjointness and measure of the major arcs, Dirichlet's theorem, the Gauss sum, the
Ramanujan sum, the singular series, `J(n)`, the geometric sum behind `T(β)`, the multiplicative
large sieve, Gallagher's density estimate for zeros near 1, Page's theorem, Siegel's theorem,
Lemmas 6, 9 and 10.
Assembly: `minor_approx`, every point of `[0, 1]` off the major arcs has an approximation
`a/q` with `P < q ≤ N/P`, the starting point of Lemma 11, p. 137.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Proof additions by Codex task189 on 2026-10-30. AI wrote the Lean code.
Proof additions by Codex task195 on 2026-10-31 UTC. AI wrote the Lean code.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.RieselVaughan1983.MuPhiSum
import LeanLab.RieselVaughan1983.GaussImprim
import LeanLab.PNTSieve.MertensUpper
import LeanLab.Linnik.U1394Fejer
import LeanLab.Linnik.HilbertCosecant
import LeanLab.HardyLittlewood1923.U1482ZeroCount
import LeanLab.RieselVaughan1983.LargeSieveSchur
import LeanLab.PNTPort.LargeSieve.Montgomery
import LeanLab.Linnik.Decomp1532a
import LeanLab.HeathBrown1985.DivisorEps
import LeanLab.Linnik.U7204Display4
import LeanLab.Zinoviev1997.TotientTail
import LeanLab.PNTPort.DirichletZF.Siegel
import LeanLab.Romanov.Decomp134
import LeanLab.PNTPort.DirichletZF.Landau
import LeanLab.PNTPort.StrongPNT.StrongPNT
import LeanLab.Romanov.TotientWeights134
import LeanLab.Linnik.Decomp1537a

namespace LeanLab.Linnik.Decomp1532b

open LeanLab.PNTPort.DirichletZF

open Finset MeasureTheory ZMod ArithmeticFunction Filter Asymptotics
open LeanLab.PNTPort.DirichletZF (siegel_zero riemannZeta_real_neg L_lift lift_ne_one lift_sq)
open scoped Topology
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov (sum_moebius_divisors)
open LeanLab.PNTPort.LargeSieve (dist0 norm_e e_add norm_geom_le)
open LeanLab.Linnik.Decomp1532a (pairs dif ordTwo)
open LeanLab.Linnik.U1434Lemma21 (sv)
open LeanLab.Linnik.U1426ChainWire (Gs)
open LeanLab.Linnik.U1412Display53 (eC)

/-- The major arcs `𝔐`, display (2) p. 127, with `Q = N/P`, so `1/(qQ) = P/(qN)`. -/
def majorArcs (N : ℕ) (P : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℕ, a ≤ q ∧ Nat.Coprime a q ∧
    |α - a / q| ≤ P / (q * N)}

/-- The Ramanujan sum `c_q(n) = Σ_{a < q, (a, q) = 1} e(an/q)`. -/
noncomputable def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ range q with Nat.Coprime a q, eC ((a : ℝ) * n / q)

/-- The singular series `𝔖(n) = Σ_{q ≥ 1} μ(q)²/φ(q)² c_q(n)`, p. 130; for g = 2 this is the
`𝔖(n)` of p. 134, with `D/φ(D) = 2`. -/
noncomputable def singSeries (n : ℤ) : ℂ :=
  ∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n

/-- `J(n) = Σ_{1 < m₁, m₂ ≤ N, m₁ - m₂ = n} (log m₁ log m₂)⁻¹`, Theorem 3, p. 127. -/
noncomputable def Jn (N : ℕ) (n : ℤ) : ℝ :=
  ∑ m ∈ Ioc 1 N ×ˢ Ioc 1 N with (m.1 : ℤ) - m.2 = n, 1 / (Real.log m.1 * Real.log m.2)

/-- The distinct zeros `ρ` of `L(s, χ)` with `Re ρ ≥ σ` and `|Im ρ| ≤ T`. -/
noncomputable def zeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}

/-- Primitive characters of conductor `q + 1 ≤ T` whose L-function vanishes somewhere in
`Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`, p. 127. -/
def excSet (b T : ℝ) : Set (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) :=
  {x | ((x.1 : ℝ) + 1 ≤ T) ∧ x.2.IsPrimitive ∧
    ∃ ρ : ℂ, x.2.LFunction ρ = 0 ∧ 1 - b / Real.log T ≤ ρ.re ∧ |ρ.im| ≤ T}

/-- LEAF. Unit U-1532. The major arcs are disjoint when `2P² < N`, i.e. `2P < Q`: two arcs about
distinct fractions `a/q`, `a'/q'` with `q, q' ≤ P` do not meet, p. 127, after display (2). -/
theorem majorArcs_disjoint {N : ℕ} {P : ℝ} (hP : 0 < P) (hPN : 2 * P ^ 2 < N)
    {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqP : (q : ℝ) ≤ P) (hqP' : (q' : ℝ) ≤ P)
    (hne : (a : ℝ) / q ≠ a' / q') {α : ℝ}
    (h1 : |α - a / q| ≤ P / (q * N)) (h2 : |α - a' / q'| ≤ P / (q' * N)) : False := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hN : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hPN
  have hcross : (a : ℤ) * q' - (a' : ℤ) * q ≠ 0 := by
    intro h
    apply hne
    apply (div_eq_div_iff hq0.ne' hq0'.ne').mpr
    exact_mod_cast (sub_eq_zero.mp h)
  have hint : (1 : ℝ) ≤ |(a : ℝ) * q' - (a' : ℝ) * q| := by
    have h := Int.one_le_abs hcross
    exact_mod_cast h
  have hdist : |(a : ℝ) / q - (a' : ℝ) / q'| ≤ P / (q * N) + P / (q' * N) := by
    calc
      _ = |(α - (a' : ℝ) / q') - (α - (a : ℝ) / q)| := by congr 1; ring
      _ ≤ |α - (a' : ℝ) / q'| + |α - (a : ℝ) / q| := abs_sub _ _
      _ ≤ _ := by linarith
  have heq : (a : ℝ) / q - (a' : ℝ) / q' =
      ((a : ℝ) * q' - (a' : ℝ) * q) / (q * q') := by field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hq0 hq0')] at hdist
  have hdist' := (div_le_iff₀ (mul_pos hq0 hq0')).mp hdist
  have heq' : (P / ((q : ℝ) * N) + P / ((q' : ℝ) * N)) * (q * q') =
      P * (q + q') / N := by field_simp <;> ring
  rw [heq'] at hdist'
  have hbound := (le_div_iff₀ hN).mp (hint.trans hdist')
  nlinarith

/-- LEAF. Unit U-1532. For `P ≥ 1`, `N ≥ 1` the major arcs have measure at most `4P²/N`,
since there are at most `2 + Σ_{2 ≤ q ≤ P} φ(q)` arcs and the arc at `a/q` has length
`2P/(qN)`, p. 127. -/
theorem volume_majorArcs_le {N : ℕ} {P : ℝ} (hP : 1 ≤ P) (hN : 1 ≤ N) :
    MeasureTheory.volume (majorArcs N P) ≤ ENNReal.ofReal (4 * P ^ 2 / N) := by
  classical
  have hP0 : 0 ≤ P := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let A : ℕ → ℕ → Set ℝ := fun q a =>
    Set.Icc ((a : ℝ) / q - P / (q * N)) ((a : ℝ) / q + P / (q * N))
  have hsub : majorArcs N P ⊆ ⋃ q ∈ Icc 1 ⌊P⌋₊, ⋃ a ∈ range (q + 1), A q a := by
    rintro α ⟨_, q, hq, hqP, a, haq, _, ha⟩
    refine Set.mem_iUnion₂.mpr ⟨q, mem_Icc.mpr ⟨hq, Nat.le_floor hqP⟩, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨a, mem_range.mpr (by omega), ?_⟩
    change _ ≤ α ∧ α ≤ _
    rw [abs_le] at ha
    constructor <;> linarith [ha.1, ha.2]
  have hA : ∀ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ range (q + 1), volume (A q a) ≤
      ENNReal.ofReal (4 * P / N) := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
    have heq : ∀ a, volume (A q a) = ENNReal.ofReal (2 * P / (q * N)) := by
      intro a
      change volume (Set.Icc _ _) = _
      rw [Real.volume_Icc]
      congr 1
      ring
    simp_rw [heq]
    simp only [sum_const, card_range, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos hq0 hN0) hN0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (mul_nonneg hP0 hN0.le)]
  calc
    volume (majorArcs N P) ≤ volume (⋃ q ∈ Icc 1 ⌊P⌋₊, ⋃ a ∈ range (q + 1), A q a) := measure_mono hsub
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, volume (⋃ a ∈ range (q + 1), A q a) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ range (q + 1), volume (A q a) :=
      sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ENNReal.ofReal (4 * P / N) := sum_le_sum hA
    _ ≤ ENNReal.ofReal (4 * P ^ 2 / N) := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hf := Nat.floor_le hP0
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hN0]
      nlinarith

/-- LEAF. Unit U-1532. Dirichlet's theorem in the form of p. 127, display (2): for
`α ∈ [0, 1]` and real `Q ≥ 1` there are `1 ≤ q ≤ Q` and `0 ≤ a ≤ q`, `(a, q) = 1`, with
`|α - a/q| ≤ 1/(qQ)`. -/
theorem exists_approx {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |α - a / q| ≤ 1 / (q * Q) := by
  have ha0 := hα.1
  have ha1 := hα.2
  have hQ0 : 0 < Q := by linarith
  have hn : 0 < ⌊Q⌋₊ := by have := Nat.le_floor (n := 1) (by simpa using hQ); omega
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  have hd0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hdenQ : (r.den : ℝ) ≤ Q :=
    (show (r.den : ℝ) ≤ ⌊Q⌋₊ by exact_mod_cast hden).trans (Nat.floor_le (by linarith))
  have hbd : |α - (r : ℝ)| ≤ 1 / (r.den * Q) := by
    refine hr.trans (one_div_le_one_div_of_le (mul_pos hd0 hQ0) ?_)
    nlinarith [Nat.lt_floor_add_one Q]
  by_cases hr0 : (r : ℝ) < 0
  · refine ⟨1, 0, by norm_num, by simpa using hQ, by norm_num, by norm_num, ?_⟩
    have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hsmall : 1 / ((r.den : ℝ) * Q) ≤ 1 / Q :=
      one_div_le_one_div_of_le hQ0 (by nlinarith)
    simp only [Nat.cast_one, Nat.cast_zero, zero_div, sub_zero, one_mul]
    rw [abs_of_nonneg hα.1]
    rw [abs_of_nonneg (by linarith : 0 ≤ α - (r : ℝ))] at hbd
    linarith
  by_cases hr1 : 1 < (r : ℝ)
  · refine ⟨1, 1, by norm_num, by simpa using hQ, by norm_num, by norm_num, ?_⟩
    have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hsmall : 1 / ((r.den : ℝ) * Q) ≤ 1 / Q :=
      one_div_le_one_div_of_le hQ0 (by nlinarith)
    simp only [Nat.cast_one, div_one, one_mul]
    rw [abs_of_nonpos (by linarith : α - 1 ≤ 0)]
    rw [abs_of_nonpos (by linarith : α - (r : ℝ) ≤ 0)] at hbd
    linarith
  have hnum0 : 0 ≤ r.num := Rat.num_nonneg.mpr (by exact_mod_cast (le_of_not_gt hr0))
  have hcast : (r.num.toNat : ℝ) / r.den = r := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum0, Rat.cast_def]
  refine ⟨r.den, r.num.toNat, r.den_pos, hdenQ, ?_, ?_, ?_⟩
  · have : (r.num.toNat : ℝ) / r.den ≤ 1 := by rw [hcast]; exact le_of_not_gt hr1
    have := (div_le_one hd0).mp this
    exact_mod_cast this
  · have he : r.num.toNat = r.num.natAbs := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg hnum0, Int.natCast_natAbs, abs_of_nonneg hnum0]
    rw [he]
    exact r.reduced
  · simpa [hcast] using hbd

/-- ASSEMBLY, CONDITIONAL ON the leaf `exists_approx`. A point of `[0, 1]` off the major arcs,
with `0 < P ≤ N`, has an approximation `a/q` in lowest terms with `P < q ≤ N/P` and
`|α - a/q| ≤ P/(qN)`; this is the start of the proof of Lemma 11, p. 137. -/
theorem minor_approx {N : ℕ} {P : ℝ} (hP : 0 < P) (hPN : P ≤ N) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hM : α ∉ majorArcs N P) :
    ∃ q a : ℕ, P < q ∧ (q : ℝ) ≤ N / P ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |α - a / q| ≤ P / (q * N) := by
  have hN : (0 : ℝ) < N := lt_of_lt_of_le hP hPN
  have hQ : 1 ≤ (N : ℝ) / P := by rw [le_div_iff₀ hP]; linarith
  obtain ⟨q, a, hq1, hqQ, haq, hcop, happ⟩ := exists_approx hα hQ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have heq : 1 / (q * ((N : ℝ) / P)) = P / (q * N) := by
    field_simp
  rw [heq] at happ
  refine ⟨q, a, ?_, hqQ, haq, hcop, happ⟩
  by_contra hle
  push Not at hle
  exact hM ⟨hα, q, hq1, hle, a, haq, hcop, happ⟩

/-- LEAF. Unit U-1532. A primitive character `χ` modulo `q` has Gauss sum of absolute value
`√q`, display (6) p. 129 in the case `q = r`. -/
theorem gaussSum_norm_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖∑ a : ZMod q, χ a * eC ((a.val : ℝ) / q)‖ ^ 2 = q := by
  have he : (∑ a : ZMod q, χ a * eC ((a.val : ℝ) / q)) = gaussSum χ ZMod.stdAddChar := by
    unfold gaussSum
    apply sum_congr rfl
    intro a _
    congr 1
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    unfold eC
    congr 1
    push_cast
    ring
  rw [he]
  classical
  have hft : ZMod.dft χ = fun k => χ⁻¹ (-k) * gaussSum χ stdAddChar := by
    ext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hχinv : χ⁻¹.IsPrimitive := by simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  have hprod : gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = (q : ℂ) * χ (-1) := by
    have h := congr_fun (ZMod.dft_dft χ) (1 : ZMod q)
    rw [hft] at h
    rw [ZMod.dft_mul_const, ZMod.dft_comp_neg] at h
    dsimp only at h
    rw [hχinv.fourierTransform_eq_inv_mul_gaussSum] at h
    simpa [mul_comm] using h
  have hstar : star (gaussSum χ stdAddChar) = χ⁻¹ (-1) * gaussSum χ⁻¹ stdAddChar := by
    rw [star_gaussSum_eq]
    simp only [gaussSum, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.neg (ZMod q))
    intro a
    simp only [Equiv.neg_apply, AddChar.inv_apply]
    rw [← mul_assoc, ← map_mul, neg_one_mul, neg_neg]
  have heq : gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = (q : ℂ) := by
    calc
      _ = (gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar) * χ⁻¹ (-1) := by rw [hstar]; ring
      _ = (q : ℂ) * (χ⁻¹ (-1) * χ (-1)) := by rw [hprod]; ring
      _ = q := by rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply isUnit_neg_one, mul_one]
  have hn := congrArg Complex.re heq
  have hn' : Complex.normSq (gaussSum χ stdAddChar) = (q : ℝ) := by
    simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.natCast_re] using hn
  rwa [Complex.normSq_eq_norm_sq] at hn'

/-- The divisor formula for the Ramanujan sum at an integer argument, p.130.
Adapted from the lab natural argument proof in PNTPort.Vinogradov.SingSeries. -/
theorem ramanujanSum_eq_divisor_sum {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujanSum q n = ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
      (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℤ) := by
  have heq : ramanujanSum q n =
      ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), LeanLab.PNTPort.LargeSieve.e (n * r / q) := by
    unfold ramanujanSum
    apply sum_congr rfl
    intro a ha
    rw [← LeanLab.Linnik.U1434Lemma21.e_eq_eC]
    congr 1
    ring
  rw [heq, Nat.gcd_comm q n.natAbs]

  rw [sum_filter]
  have step1 : ∀ r ∈ range q, (if Nat.Coprime r q then LeanLab.PNTPort.LargeSieve.e (n * r / q) else 0) =
      ∑ d ∈ (Nat.gcd r q).divisors, (μ d : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * r / q) := by
    intro r _
    rw [← sum_mul, sum_moebius_divisors]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl step1]
  rw [sum_comm' (t' := q.divisors) (s' := fun d => (range q).filter (fun r => d ∣ r))]
  · have step2 : ∀ d ∈ q.divisors, ∑ r ∈ (range q).filter (fun r => d ∣ r), (μ d : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * r / q)
        = (μ d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ n then ((q / d : ℕ) : ℂ) else 0) := by
      intro d hd
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0
      rw [← mul_sum, ← LeanLab.PNTPort.LargeSieve.sum_e_mul_div n hqd]
      congr 1
      refine sum_nbij' (fun r => r / d) (fun s => d * s) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        rw [mem_filter, mem_range] at hr
        rw [mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [mem_range] at hs
        rw [mem_filter, mem_range]
        refine ⟨?_, dvd_mul_right d s⟩
        have := Nat.mul_lt_mul_of_pos_left hs hd0
        rwa [Nat.mul_div_cancel' hdq] at this
      · intro r hr
        rw [mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _; exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        rw [mem_filter] at hr
        obtain ⟨s, rfl⟩ := hr.2
        rw [Nat.mul_div_cancel_left s hd0, Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
        congr 1
        push_cast
        field_simp
    rw [sum_congr rfl step2]
    -- reindex d ↦ q / d onto the divisors of gcd(n, q)
    rw [← sum_filter_add_sum_filter_not q.divisors (fun d => ((q / d : ℕ) : ℤ) ∣ n)]
    rw [sum_eq_zero (s := q.divisors.filter (fun d => ¬ ((q / d : ℕ) : ℤ) ∣ n))
      (fun d hd => by rw [mem_filter] at hd; rw [if_neg hd.2, mul_zero]), add_zero]
    refine sum_nbij' (fun d => q / d) (fun e => q / e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mem_divisors]
      refine ⟨Nat.dvd_gcd (Int.natCast_dvd.mp hd.2) (Nat.div_dvd_of_dvd hd.1.1), ?_⟩
      exact (Nat.gcd_pos_of_pos_right n.natAbs (by omega)).ne'
    · intro e he
      rw [Nat.mem_divisors] at he
      have heq : e ∣ q := (Nat.dvd_gcd_iff.1 he.1).2
      have hen : e ∣ n.natAbs := (Nat.dvd_gcd_iff.1 he.1).1
      have he0 : 0 < e := Nat.pos_of_dvd_of_pos heq (by omega)
      rw [mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd heq, by omega⟩, ?_⟩
      rw [Nat.div_div_self heq (by omega)]; exact Int.natCast_dvd.mpr hen
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 (by omega)
    · intro e he
      rw [Nat.mem_divisors] at he
      exact Nat.div_div_self (Nat.dvd_gcd_iff.1 he.1).2 (by omega)
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [if_pos hd.2, Nat.div_div_self hd.1.1 (by omega)]
      ring
  · intro r d
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h3, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, by omega⟩


/-- LEAF. Unit U-1532. For squarefree `q`, `c_q(n) = μ(q/(q, n)) φ((q, n))`, the fact used on
p. 130 before display (11). -/
theorem ramanujanSum_squarefree {q : ℕ} (hq : Squarefree q) (n : ℤ) :
    ramanujanSum q n =
      ((ArithmeticFunction.moebius (q / Nat.gcd q n.natAbs) : ℤ) : ℂ) *
        ((Nat.gcd q n.natAbs).totient : ℂ) := by
  classical
  rw [ramanujanSum_eq_divisor_sum (Nat.pos_of_ne_zero hq.ne_zero) n]
  generalize hgdef : Nat.gcd q n.natAbs = g
  have hg : g ∣ q := hgdef ▸ Nat.gcd_dvd_left q n.natAbs
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hq.ne_zero hg
  have hcop : Nat.Coprime (q / g) g := Nat.coprime_of_squarefree_mul (by rwa [Nat.div_mul_cancel hg])
  have hsum : (∑ d ∈ g.divisors, (d : ℂ) * (moebius (g / d) : ℤ)) = (g.totient : ℂ) := by
    have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℂ) (f := fun n => (n.totient : ℂ))
      (g := fun n => (n : ℂ))).mp (by intro n hn; exact_mod_cast Nat.sum_totient n) g (Nat.pos_of_ne_zero hg0)
    rw [Nat.sum_divisorsAntidiagonal' (fun a b => (moebius a : ℂ) * (b : ℂ))] at h
    simpa only [mul_comm] using h
  calc
    _ = ∑ d ∈ g.divisors, (moebius (q / g) : ℂ) * ((d : ℂ) * (moebius (g / d) : ℂ)) := by
      apply sum_congr rfl
      intro d hd
      have hdg := Nat.dvd_of_mem_divisors hd
      have heq : q / d = (q / g) * (g / d) := by rw [← Nat.mul_div_assoc _ hdg, Nat.div_mul_cancel hg]
      rw [heq, isMultiplicative_moebius.map_mul_of_coprime (hcop.of_dvd_right (Nat.div_dvd_of_dvd hdg))]
      push_cast
      ring
    _ = _ := by rw [← mul_sum, hsum]

/-- The literal numerator n printed on p.130 fails at q = 2 and n = 1. -/
theorem printed_ramanujan_formula_two_one_ne : ramanujanSum 2 1 ≠
    ((ArithmeticFunction.moebius (1 / Nat.gcd 2 (1 : ℤ).natAbs) : ℤ) : ℂ) *
      ((Nat.gcd 2 (1 : ℤ).natAbs).totient : ℂ) := by
  rw [ramanujanSum_squarefree Nat.squarefree_two]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- LEAF. Unit U-1532. For `n ≠ 0` the series `Σ_q μ(q)²/φ(q)² c_q(n)` defining `𝔖(n)`
converges absolutely, p. 130. -/
theorem summable_singSeries {n : ℤ} (hn : n ≠ 0) :
    Summable fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n := by
  classical
  let B : ℝ := ∑ d ∈ n.natAbs.divisors, (d : ℝ)
  have hB : 0 ≤ B := sum_nonneg fun d hd => Nat.cast_nonneg d
  have hnn : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hR (q : ℕ) : ‖ramanujanSum q n‖ ≤ B := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simpa [ramanujanSum] using hB
    rw [ramanujanSum_eq_divisor_sum hq n]
    calc
      _ ≤ ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
          ‖(d : ℂ) * (moebius (q / d) : ℤ)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ (Nat.gcd q n.natAbs).divisors, (d : ℝ) := by
        apply sum_le_sum
        intro d hd
        rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
        have hmu := ArithmeticFunction.abs_moebius_le_one (n := q / d)
        have hmu' : |((moebius (q / d) : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hmu
        exact mul_le_of_le_one_right (Nat.cast_nonneg d) hmu'
      _ ≤ B := sum_le_sum_of_subset_of_nonneg
        (Nat.divisors_subset_of_dvd hnn (Nat.gcd_dvd_right q n.natAbs)) (by intros; positivity)
  have hs : Summable (fun q : ℕ => (7 * B) * (q : ℝ) ^ (-(7 : ℝ) / 4)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(7 : ℝ) / 4 < -1)).mul_left _
  apply hs.of_norm_bounded
  intro q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hmu : ‖((moebius q : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
    have h : ‖((moebius q : ℤ) : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_intCast] using
        (show |((moebius q : ℤ) : ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q))
    nlinarith [norm_nonneg (((moebius q : ℤ) : ℂ))]
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 2) * B :=
      mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) (hR q) (norm_nonneg _) (by positivity)
    _ ≤ (7 * (q : ℝ) ^ (-(7 : ℝ) / 4)) * B :=
      mul_le_mul_of_nonneg_right (LeanLab.Zinoviev1997.inv_totient_sq_seven q hq) hB
    _ = _ := by ring

/-- LEAF. Unit U-1532. For g = 2 the singular series vanishes at odd `n`: the Euler factor at
`p = 2` is `1 + c_2(n) = 0`; p. 134, the remark that only `n` with `D ∣ n` occur. -/
theorem singSeries_odd {n : ℤ} (hn : Odd n) : singSeries n = 0 := by
  classical
  let f : ℕ → ℂ := fun q => (μ q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n
  have hn0 : n ≠ 0 := by intro h; subst n; norm_num at hn
  have hs : Summable f := summable_singSeries hn0
  have hn2 : Nat.Coprime 2 n.natAbs := Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hn)
  have hzero {q : ℕ} (hq : ¬ Squarefree q) : f q = 0 := by
    simp [f, moebius_eq_zero_of_not_squarefree hq]
  have hfour (q : ℕ) : f (4 * q) = 0 := by
    apply hzero
    intro hsq
    have hdiv : 2 * 2 ∣ 4 * q := by omega
    exact (by norm_num : ¬IsUnit (2 : ℕ)) (hsq 2 hdiv)
  have hpair (r : ℕ) (hr : Odd r) : f (2 * r) = -f r := by
    by_cases hsq : Squarefree r
    · have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
      have hsq2 : Squarefree (2 * r) := (Nat.squarefree_mul hcop).mpr ⟨Nat.squarefree_two, hsq⟩
      have hg : Nat.gcd (2 * r) n.natAbs = Nat.gcd r n.natAbs := hn2.gcd_mul_left_cancel r
      have hcopdiv : Nat.Coprime 2 (r / Nat.gcd r n.natAbs) :=
        hcop.of_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r n.natAbs))
      have hdiv : 2 * r / Nat.gcd r n.natAbs = 2 * (r / Nat.gcd r n.natAbs) :=
        Nat.mul_div_assoc 2 (Nat.gcd_dvd_left r n.natAbs)
      have hm1 : (μ r : ℂ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq
      have hm2 : (μ (2 * r) : ℂ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq2
      dsimp [f]
      rw [ramanujanSum_squarefree hsq2 n, ramanujanSum_squarefree hsq n, hg,
        Nat.totient_mul hcop, hdiv, isMultiplicative_moebius.map_mul_of_coprime hcopdiv,
        hm2, hm1]
      norm_num [moebius_apply_prime Nat.prime_two]
    · rw [hzero hsq, hzero (fun h => hsq h.of_mul_right), neg_zero]
  have he : Summable (fun k => f (2 * k)) := hs.comp_injective (i := fun k : ℕ => 2 * k) (by
    intro a b h; change 2 * a = 2 * b at h; omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hs.comp_injective (i := fun k : ℕ => 2 * k + 1) (by
    intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hee : Summable (fun k => f (2 * (2 * k))) := hs.comp_injective (i := fun k : ℕ => 2 * (2 * k)) (by
    intro a b h; change 2 * (2 * a) = 2 * (2 * b) at h; omega)
  have heo : Summable (fun k => f (2 * (2 * k + 1))) := hs.comp_injective (i := fun k : ℕ => 2 * (2 * k + 1)) (by
    intro a b h; change 2 * (2 * a + 1) = 2 * (2 * b + 1) at h; omega)
  have hsplit := tsum_even_add_odd (f := f) he ho
  have hsplit2 := tsum_even_add_odd (f := fun k => f (2 * k)) hee heo
  have heq0 : (∑' k, f (2 * (2 * k))) = 0 := by simp [show ∀ k, 2 * (2 * k) = 4 * k by intro k; omega, hfour]
  have heqneg : (∑' k, f (2 * (2 * k + 1))) = -(∑' k, f (2 * k + 1)) := by
    simp_rw [hpair (2 * _ + 1) (by exact ⟨_, rfl⟩)]
    exact tsum_neg
  change (∑' q, f q) = 0
  rw [heq0, heqneg, zero_add] at hsplit2
  rw [hsplit2.symm] at hsplit
  simpa using hsplit.symm

/-- The diagonal identity for J of zero, p.127 and p.130. -/
theorem Jn_zero_eq_sum (N : ℕ) : Jn N 0 = ∑ a ∈ Ioc 1 N, 1 / Real.log a ^ 2 := by
  classical
  unfold Jn
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro a ha
  rw [sum_eq_single_of_mem a ha]
  · simp [pow_two]
  · intro b hb hba
    have hne : (a : ℤ) - b ≠ 0 := by omega
    simp [hne]


/-- LEAF. Unit U-1532. `J(n) ≤ J(0)` for every `n`, by Cauchy-Schwarz; p. 130, the line
`J(n) ≤ J(0) ∼ N/log² N`. -/
theorem Jn_le_J0 (N : ℕ) (n : ℤ) : Jn N n ≤ Jn N 0 := by
  classical
  let T := (Ioc 1 N ×ˢ Ioc 1 N).filter (fun m => (m.1 : ℤ) - m.2 = n)
  let f : ℕ → ℝ := fun a => 1 / Real.log a
  have hJ0 : Jn N 0 = ∑ a ∈ Ioc 1 N, f a ^ 2 := by
    unfold Jn
    rw [sum_filter, sum_product]
    apply sum_congr rfl
    intro a ha
    rw [sum_eq_single_of_mem a ha]
    · simp [f, pow_two]
    · intro b hb hba
      have hne : (a : ℤ) - b ≠ 0 := by omega
      simp [hne]
  have hfst : Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Prod.ext hab
    omega
  have hsnd : Set.InjOn Prod.snd (T : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Prod.ext _ hab
    omega
  have hproj : ∀ (p : ℕ × ℕ → ℕ), Set.InjOn p (T : Set (ℕ × ℕ)) →
      (∀ a ∈ T, p a ∈ Ioc 1 N) → (∑ a ∈ T, f (p a) ^ 2) ≤ ∑ a ∈ Ioc 1 N, f a ^ 2 := by
    intro p hinj hmem
    apply sum_le_sum_of_injOn p hinj
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact hmem b hb
    · intro a ha; exact le_rfl
    · intro a ha _; positivity
  have hleft := hproj Prod.fst hfst (fun a ha => (mem_product.mp (mem_filter.mp ha).1).1)
  have hright := hproj Prod.snd hsnd (fun a ha => (mem_product.mp (mem_filter.mp ha).1).2)
  have hterm : Jn N n ≤ (∑ a ∈ T, (f a.1 ^ 2 + f a.2 ^ 2)) / 2 := by
    unfold Jn
    change (∑ a ∈ T, 1 / (Real.log a.1 * Real.log a.2)) ≤ _
    rw [sum_div]
    apply sum_le_sum
    intro a ha
    have hsq := sq_nonneg (f a.1 - f a.2)
    have heq : 1 / (Real.log a.1 * Real.log a.2) = f a.1 * f a.2 := by simp [f, mul_comm]
    rw [heq]
    nlinarith
  rw [hJ0]
  rw [sum_add_distrib] at hterm
  linarith

/-- The lower estimate underlying J of zero asymptotic, p.130. -/
theorem J0_lower {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ) - 1) / Real.log N ^ 2 ≤ Jn N 0 := by
  rw [Jn_zero_eq_sum]
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have heq : ((N : ℝ) - 1) / Real.log N ^ 2 = ∑ a ∈ Ioc 1 N, 1 / Real.log N ^ 2 := by
    simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    rw [Nat.cast_sub hN1, Nat.cast_one]
    ring
  rw [heq]
  apply sum_le_sum
  intro a ha
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
  have haN : (a : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp ha).2
  have hapos : 0 < Real.log a := Real.log_pos ha1
  have halog : Real.log a ≤ Real.log N := Real.log_le_log (by positivity) haN
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hapos.le halog 2)

/-- LEAF. Unit U-1532. `J(0) = Σ_{1 < m ≤ N} 1/log² m ∼ N/log² N`, p. 130. -/
theorem J0_asymp :
    Filter.Tendsto (fun N : ℕ => Jn N 0 / ((N : ℝ) / Real.log N ^ 2)) Filter.atTop (nhds 1) := by
  let F : ℕ → ℝ := fun n => (n : ℝ) / Real.log n ^ 2
  let g : ℕ → ℝ := fun n => 1 / Real.log (n + 1) ^ 2
  let d : ℕ → ℝ := fun n => F (n + 1) - F n
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (nhds 0) := hlog.inv_tendsto_atTop
  have hdiff := Real.tendsto_log_nat_add_one_sub_log
  let T : ℕ → ℝ := fun n => (n : ℝ) * (Real.log (n + 1) - Real.log n) *
    (Real.log (n + 1) + Real.log n) / Real.log n ^ 2
  have hb : Tendsto (fun n : ℕ => (Real.log (n + 1) - Real.log n) / Real.log n ^ 2 + 2 / Real.log n)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hdiff.mul (hi.pow 2)).add (hi.const_mul 2)
  have hT : Tendsto T atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ => (Real.log (n + 1) - Real.log n) / Real.log n ^ 2 + 2 / Real.log n)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      dsimp [T]
      exact div_nonneg (mul_nonneg (mul_nonneg hn0.le (sub_nonneg.mpr hmono)) (by linarith)) (sq_nonneg _)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      have hbd : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < (n : ℝ) + 1) hn0)
        rw [Real.log_div (by positivity) hn0.ne', show ((n : ℝ) + 1) / n - 1 = 1 / n by field_simp; ring] at h
        have h' := (le_div_iff₀ hn0).mp h
        nlinarith
      dsimp [T]
      calc
        _ ≤ (Real.log ((n : ℝ) + 1) + Real.log n) / Real.log n ^ 2 := by
          exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (by linarith) hbd) (by positivity)
        _ = _ := by field_simp; ring
    · exact hb
  have hd : Tendsto (fun n => d n / g n) atTop (nhds 1) := by
    have hh : Tendsto (fun n => 1 - T n) atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hT
    norm_num only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    have hl1 : Real.log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne'
    dsimp [d, g, F, T]
    push_cast
    field_simp
    <;> ring
  have herr : (fun n => d n - g n) =o[atTop] g := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · have hh : Tendsto (fun n => d n / g n - 1) atTop (nhds (1 - 1)) := hd.sub tendsto_const_nhds
      norm_num only [sub_self] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hg : g n ≠ 0 := by
        dsimp [g]
        exact one_div_ne_zero (pow_ne_zero 2 (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne')
      dsimp [d]
      field_simp
      <;> ring
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hg : g n ≠ 0 := by
        dsimp [g]
        exact one_div_ne_zero (pow_ne_zero 2 (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne')
      exact fun h => (hg h).elim
  have hsum (N : ℕ) : (∑ i ∈ range N, g i) = Jn N 0 := by
    rw [Jn_zero_eq_sum]
    have hshift : (∑ i ∈ range N, g i) = ∑ a ∈ Ico 1 (N + 1), 1 / Real.log a ^ 2 := by
      simpa only [g, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm] using
        (sum_Ico_eq_sum_range (fun a : ℕ => 1 / Real.log a ^ 2) 1 (N + 1)).symm
    rw [hshift]
    by_cases hN : N = 0
    · subst N; simp
    have hset : Ico 1 (N + 1) = insert 1 (Ioc 1 N) := by ext a; simp; omega
    rw [hset, sum_insert (by simp)]
    simp
  have hdiv0 : Tendsto (fun n : ℕ => Real.log n ^ 2 / ((n : ℝ) - 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul, sub_eq_add_neg] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hdivpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log n ^ 2 / ((n : ℝ) - 1) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hbig : Tendsto (fun n : ℕ => ((n : ℝ) - 1) / Real.log n ^ 2) atTop atTop := by
    have hh := (tendsto_nhdsWithin_iff.mpr ⟨hdiv0, hdivpos⟩).inv_tendsto_nhdsGT_zero
    change Tendsto (fun n : ℕ => (Real.log n ^ 2 / ((n : ℝ) - 1))⁻¹) atTop atTop at hh
    simpa only [inv_div] using hh
  have hsumtop : Tendsto (fun N => ∑ i ∈ range N, g i) atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hbig
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [hsum]
    exact J0_lower hN
  have hsmall := (herr.sum_range (by intro n; dsimp [g]; positivity) hsumtop).tendsto_div_nhds_zero
  have hratio : Tendsto (fun N => F N / Jn N 0) atTop (nhds 1) := by
    have hh : Tendsto (fun N => (∑ i ∈ range N, (d i - g i)) / (∑ i ∈ range N, g i) + 1) atTop (nhds (0 + 1)) := hsmall.add tendsto_const_nhds
    norm_num only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [sum_sub_distrib, show (∑ i ∈ range N, d i) = F N - F 0 from sum_range_sub F N, hsum] 
    have hJ : Jn N 0 ≠ 0 := by
      have h := J0_lower hN
      have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
      have hl : 0 < Real.log (N : ℝ) := Real.log_pos hN1
      exact ne_of_gt (lt_of_lt_of_le (by positivity) h)
    have hf0 : F 0 = 0 := by simp [F]
    rw [hf0, sub_zero]
    field_simp
    <;> ring
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [F] using hinv

/-- LEAF. Unit U-1532. The geometric sum bound `|Σ_{m ≤ x} e(mβ)| ≤ 1/(2‖β‖)` for `β` not an
integer, `‖β‖` the distance to the nearest integer; p. 130, the estimate of `T(β)`. -/
theorem norm_geom_sum_le (x : ℕ) {β : ℝ} (hβ : Int.fract β ≠ 0) :
    ‖∑ m ∈ Icc 1 x, eC (m * β)‖ ≤ 1 / (2 * min (Int.fract β) (1 - Int.fract β)) := by
  simp_rw [← LeanLab.Linnik.U1434Lemma21.e_eq_eC]
  have hd : dist0 β = min (Int.fract β) (1 - Int.fract β) := abs_sub_round_eq_min β
  have hp : 0 < dist0 β := by
    rw [hd, lt_min_iff]
    exact ⟨lt_of_le_of_ne (Int.fract_nonneg β) (Ne.symm hβ), sub_pos.mpr (Int.fract_lt_one β)⟩
  have heq : (∑ m ∈ Icc 1 x, LeanLab.PNTPort.LargeSieve.e (m * β)) = LeanLab.PNTPort.LargeSieve.e β * ∑ m ∈ range x, LeanLab.PNTPort.LargeSieve.e (m * β) := by
    rw [show Icc 1 x = Ico 1 (x + 1) by ext k; simp]
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_sum]
    apply sum_congr rfl
    intro m _
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [heq, norm_mul, norm_e, one_mul, ← hd]
  exact norm_geom_le x hp

/-- The weaker lab coefficient alone does not imply the sharp coefficient on p.131. -/
theorem weaker_large_sieve_constant_insufficient (N Q : ℕ) (hQ : 0 < Q) :
    ∃ B : ℝ, B ≤ (N : ℝ) + 2 * (Q : ℝ) ^ 2 ∧ (N : ℝ) + (Q : ℝ) ^ 2 < B := by
  refine ⟨(N : ℝ) + 2 * (Q : ℝ) ^ 2, le_rfl, ?_⟩
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := lt_add_of_pos_right ((N : ℝ) + (Q : ℝ) ^ 2) (sq_pos_of_pos hq)
  convert h using 1 <;> ring

/-- The modulus one case of the large sieve input on p.131, by Cauchy Schwarz. -/
theorem large_sieve_level_one (a : ℕ → ℂ) (M N : ℕ) :
    ∑ q ∈ Icc (1 : ℕ) 1, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + 1) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  have hchars : (univ : Finset (DirichletCharacter ℂ 1)) = {1} := by
    ext χ
    simp only [mem_univ, mem_singleton, true_iff]
    exact DirichletCharacter.level_one χ
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  simp only [Icc_self, sum_singleton, Nat.cast_one, Nat.totient_one, div_one, one_mul]
  rw [hchars]
  simp only [filter_singleton, DirichletCharacter.isPrimitive_one_level_one, ite_true, sum_singleton,
    hone, mul_one]
  have hnorm : ‖∑ n ∈ Ioc M (M + N), a n‖ ^ 2 ≤ (∑ n ∈ Ioc M (M + N), ‖a n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have hc := sq_sum_le_card_mul_sum_sq (s := Ioc M (M + N)) (f := fun n => ‖a n‖)
  have hc' : (∑ n ∈ Ioc M (M + N), ‖a n‖) ^ 2 ≤
      (N : ℝ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by simpa using hc
  exact (hnorm.trans hc').trans (mul_le_mul_of_nonneg_right (by linarith) (sum_nonneg fun _ _ => sq_nonneg _))

/-- Gallagher p.131 character orthogonality reduces the multiplicative sieve to additive sums. -/
theorem primitive_sieve_le_additive (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), (starRingEnd ℂ) (a n) * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 := by
  classical
  apply sum_le_sum
  intro q hq
  letI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  let I : Finset ℤ := (Ioc M (M + N)).map emb
  let az : ℤ → ℂ := fun z => a z.toNat
  have h := LeanLab.PNTPort.LargeSieve.prim_chars_le I az (q := q)
  simpa only [I, az, sum_map, emb, Function.Embedding.coeFn_mk,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast, Int.cast_ofNat] using h

/-- At real part at least one a primitive character has no zeros. This closes the endpoint
of the p.131 density estimate. -/
theorem zeroCount_eq_zero_of_one_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) : zeroCount χ σ T = 0 := by
  have hne (ρ : ℂ) (hρ : σ ≤ ρ.re) : χ.LFunction ρ ≠ 0 := by
    by_cases hχ : χ = 1
    · have hq : q = 1 := by
        have hh := hp
        rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at hh
        exact hh.symm
      subst q
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re (hσ.trans hρ)
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (hσ.trans hρ)
  have he : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} = ∅ := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hz, hβ, ht⟩
    exact hne ρ hβ hz
  simp only [zeroCount, he, Set.ncard_empty]

/-- The primitive family count vanishes at the sigma one endpoint of p.131. -/
theorem density_sum_at_one (T : ℝ) :
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ 1 T : ℝ) = 0 := by
  classical
  apply sum_eq_zero
  intro q hq
  apply sum_eq_zero
  intro χ hχ
  rw [zeroCount_eq_zero_of_one_le χ (mem_filter.mp hχ).2 le_rfl, Nat.cast_zero]

/-- Gallagher 1975 p.131. Auxiliary exact diagonal and off-diagonal Fourier energy identity. -/
theorem fourier_energy_split {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : Finset ℤ) (α : ι → ℝ) (b : ι → ℂ) :
    ∑ n ∈ t, ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 =
      (t.card : ℝ) * ∑ r ∈ s, ‖b r‖ ^ 2 +
      ∑ r ∈ s, ∑ r' ∈ s.erase r,
        (b r * (starRingEnd ℂ) (b r') *
          ∑ n ∈ t, LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
  classical
  have hn (n : ℤ) : ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 =
      ∑ r ∈ s, ∑ r' ∈ s, (b r * (starRingEnd ℂ) (b r') *
        LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
    have h := congrArg Complex.re (LeanLab.PNTPort.LargeSieve.normSq_dualSum s α b n)
    simpa only [LeanLab.PNTPort.LargeSieve.dualSum, Complex.ofReal_re, Complex.re_sum] using h
  simp_rw [hn]
  rw [sum_comm]
  have hr (r : ι) (hr : r ∈ s) :
      (∑ n ∈ t, ∑ r' ∈ s,
        (b r * (starRingEnd ℂ) (b r') *
          LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re) =
      (t.card : ℝ) * ‖b r‖ ^ 2 + ∑ r' ∈ s.erase r,
        (b r * (starRingEnd ℂ) (b r') *
          ∑ n ∈ t, LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
    rw [sum_comm]
    rw [← sum_erase_add _ _ hr]
    simp only [sub_self, mul_zero, LeanLab.PNTPort.LargeSieve.e_zero, mul_one,
      Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, sum_const, nsmul_eq_mul]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro r' hr'
    rw [mul_sum, Complex.re_sum]
  rw [sum_congr rfl hr, sum_add_distrib, mul_sum]

/-- Montgomery and Vaughan 1974 pp.73 to 82. Auxiliary normalization of the circular kernel. -/
theorem circular_kernel_eq_cosecant (θ : ℝ) :
    LeanLab.PNTPort.LargeSieve.e (θ / 2) /
        (LeanLab.PNTPort.LargeSieve.e θ - 1) =
      1 / (2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ)) := by
  have hx : LeanLab.PNTPort.LargeSieve.e θ =
      LeanLab.PNTPort.LargeSieve.e (θ / 2) ^ 2 := by
    rw [pow_two, ← e_add]
    congr 1
    ring
  have he : LeanLab.PNTPort.LargeSieve.e (θ / 2) ≠ 0 :=
    Complex.exp_ne_zero _
  have hs : LeanLab.PNTPort.LargeSieve.e (θ / 2) -
      (LeanLab.PNTPort.LargeSieve.e (θ / 2))⁻¹ =
      2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    have harg : Complex.I * ((2 * Real.pi * (θ / 2) : ℝ) : ℂ) =
        (Real.pi * θ : ℂ) * Complex.I := by push_cast; ring
    simp only [harg]
    rw [← Complex.exp_neg]
    rw [show -((Real.pi * θ : ℂ) * Complex.I) =
      (-((Real.pi * θ : ℂ))) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_mul, ← Complex.ofReal_sin]
    ring
  have hd : LeanLab.PNTPort.LargeSieve.e θ - 1 =
      LeanLab.PNTPort.LargeSieve.e (θ / 2) *
        (2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ)) := by
    rw [← hs, mul_sub, mul_inv_cancel₀ he, ← pow_two, ← hx]
  rw [hd, div_mul_eq_div_div, div_self he]

/-- Gallagher 1975 p.131. Auxiliary absolute bound for the normalized circular kernel. -/
theorem circular_kernel_norm_le {θ δ : ℝ} (hδ : 0 < δ) (hθ : δ ≤ dist0 θ) :
    ‖LeanLab.PNTPort.LargeSieve.e (θ / 2) /
      (LeanLab.PNTPort.LargeSieve.e θ - 1)‖ ≤ 1 / (4 * δ) := by
  rw [norm_div, norm_e]
  apply one_div_le_one_div_of_le (by positivity)
  exact (mul_le_mul_of_nonneg_left hθ (by norm_num)).trans
    (LeanLab.PNTPort.LargeSieve.four_dist0_le θ)


/-- Gallagher 1975 p.131. The circular Hilbert constant for at most three spaced points
follows from the absolute kernel estimate and the proved symmetric Schur inequality. -/
theorem circular_hilbert_small_family {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ) (hcard : s.card ≤ 3) (b : ι → ℂ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  classical
  let K : ι → ι → ℝ := fun r r' => if r = r' then 0 else 1 / (4 * δ)
  have hK0 : ∀ r r', 0 ≤ K r r' := by intro r r'; dsimp [K]; split_ifs <;> positivity
  have hKsym : ∀ r r', K r r' = K r' r := by
    intro r r'
    simp only [K]
    split_ifs <;> simp_all
  have hrow (r : ι) (hr : r ∈ s) : ∑ r' ∈ s, K r r' ≤ 1 / (2 * δ) := by
    rw [← sum_erase_add _ _ hr]
    have he : ∑ r' ∈ s.erase r, K r r' = ((s.erase r).card : ℝ) * (1 / (4 * δ)) := by
      calc
        _ = ∑ _r' ∈ s.erase r, (1 / (4 * δ)) := by
          apply sum_congr rfl
          intro r' hr'
          exact if_neg (mem_erase.mp hr').1.symm
        _ = _ := by simp
    rw [he]
    simp only [K, if_pos rfl, add_zero]
    have hc : ((s.erase r).card : ℝ) ≤ 2 := by
      have hh := card_erase_of_mem hr
      exact_mod_cast (by omega : (s.erase r).card ≤ 2)
    calc
      _ ≤ 2 * (1 / (4 * δ)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hnorm : ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      ∑ r ∈ s, ∑ r' ∈ s, ‖b r‖ * ‖b r'‖ * K r r' := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro r hr
    apply (norm_sum_le _ _).trans
    have heq : (∑ r' ∈ s, ‖b r‖ * ‖b r'‖ * K r r') =
        ∑ r' ∈ s.erase r, ‖b r‖ * ‖b r'‖ * K r r' := by
      rw [← sum_erase_add _ _ hr]
      simp [K]
    rw [heq]
    apply sum_le_sum
    intro r' hr'
    rw [norm_mul, norm_mul, Complex.norm_conj]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change _ ≤ if r = r' then 0 else 1 / (4 * δ)
    rw [if_neg (mem_erase.mp hr').1.symm]
    exact circular_kernel_norm_le hδ (hs r hr r' (mem_erase.mp hr').2 (mem_erase.mp hr').1.symm)
  calc
    _ ≤ _ := hnorm
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * ∑ r' ∈ s, K r r' :=
      LeanLab.PNTPort.LargeSieve.sum_sum_mul_le s (fun r => ‖b r‖) K hK0 hKsym
    _ ≤ ∑ r ∈ s, ‖b r‖ ^ 2 * (1 / (2 * δ)) :=
      sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hrow r hr) (sq_nonneg _))
    _ = _ := by rw [← sum_mul, mul_comm]

/-- Gallagher 1975 p.131. Auxiliary endpoint form of the finite geometric kernel. -/
theorem geometric_kernel_endpoints (M : ℤ) (N : ℕ) {θ : ℝ}
    (hθ : 0 < dist0 θ) :
    ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * θ) =
      (LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + N + 1 / 2) * θ) -
        LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 / 2) * θ)) *
        (LeanLab.PNTPort.LargeSieve.e (θ / 2) /
          (LeanLab.PNTPort.LargeSieve.e θ - 1)) := by
  have hpos : 0 < ‖LeanLab.PNTPort.LargeSieve.e θ - 1‖ :=
    lt_of_lt_of_le (by linarith) (LeanLab.PNTPort.LargeSieve.four_dist0_le θ)
  have hne : LeanLab.PNTPort.LargeSieve.e θ ≠ 1 := by
    intro h
    simp [h] at hpos
  have hk : (∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * θ)) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) *
        ∑ k ∈ range N, LeanLab.PNTPort.LargeSieve.e (k * θ) := by
    rw [Int.Ioc_eq_finset_map, sum_map]
    simp only [add_sub_cancel_left, Int.toNat_natCast, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [← e_add]
    congr 1
    push_cast
    ring
  have he1 : LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + N + 1 / 2) * θ) *
        LeanLab.PNTPort.LargeSieve.e (θ / 2) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) *
        LeanLab.PNTPort.LargeSieve.e (N * θ) := by
    rw [← e_add, ← e_add]
    congr 1
    ring
  have he0 : LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 / 2) * θ) *
        LeanLab.PNTPort.LargeSieve.e (θ / 2) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) := by
    rw [← e_add]
    congr 1
    ring
  rw [hk]
  simp_rw [LeanLab.PNTPort.LargeSieve.e_nat_mul]
  rw [geom_sum_eq hne]
  simp only [← mul_div_assoc, sub_mul, mul_sub, mul_one]
  rw [← LeanLab.PNTPort.LargeSieve.e_nat_mul, he1, he0]

/-- Gallagher 1975 p.131. The circular Hilbert bound controls both endpoints of the
geometric kernel. CONDITIONAL ON the supplied circular Hilbert bound. -/
theorem offdiagonal_bound_of_hilbert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (hh : ∀ v : ι → ℂ,
      ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        v r * (starRingEnd ℂ) (v r') *
          (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
            (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
        (1 / (2 * δ)) * ∑ r ∈ s, ‖v r‖ ^ 2)
    (b : ι → ℂ) (M : ℤ) (N : ℕ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N),
          LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))‖ ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  classical
  let H : (ι → ℂ) → ℂ := fun v => ∑ r ∈ s, ∑ r' ∈ s.erase r,
    v r * (starRingEnd ℂ) (v r') *
      (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
        (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))
  let v : ℝ → ι → ℂ := fun u r => b r * LeanLab.PNTPort.LargeSieve.e (u * α r)
  have hphase (u : ℝ) (r r' : ι) :
      v u r * (starRingEnd ℂ) (v u r') = b r * (starRingEnd ℂ) (b r') *
        LeanLab.PNTPort.LargeSieve.e (u * (α r - α r')) := by
    simp only [v, map_mul, ← LeanLab.PNTPort.LargeSieve.e_neg]
    rw [show u * (α r - α r') = u * α r + -(u * α r') by ring, e_add]
    ring
  have henergy (u : ℝ) : ∑ r ∈ s, ‖v u r‖ ^ 2 = ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simp only [v, norm_mul, norm_e, mul_one]
  have hH (u : ℝ) : ‖H (v u)‖ ≤ (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [henergy] using hh (v u)
  have heq : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))) =
      H (v ((M : ℝ) + N + 1 / 2)) - H (v ((M : ℝ) + 1 / 2)) := by
    simp only [H, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro r' hr'
    have hθ : 0 < dist0 (α r - α r') :=
      hδ.trans_le (hs r hr r' (mem_erase.mp hr').2 (mem_erase.mp hr').1.symm)
    rw [geometric_kernel_endpoints M N hθ, hphase, hphase]
    ring
  rw [heq]
  calc
    _ ≤ ‖H (v ((M : ℝ) + N + 1 / 2))‖ + ‖H (v ((M : ℝ) + 1 / 2))‖ := norm_sub_le _ _
    _ ≤ (1 / (2 * δ)) * (∑ r ∈ s, ‖b r‖ ^ 2) +
        (1 / (2 * δ)) * (∑ r ∈ s, ‖b r‖ ^ 2) := add_le_add (hH _) (hH _)
    _ = _ := by ring

/-- Montgomery and Vaughan 1974 pp.73 to 82. The classical cosecant estimate gives the
normalized circular estimate with its exact factor one half. CONDITIONAL ON the supplied
cosecant estimate. Gallagher 1975 p.131 uses the resulting sampling bound. -/
theorem circular_hilbert_of_cosecant {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (b : ι → ℂ)
    (hh : ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        b r * (starRingEnd ℂ) (b r') /
          (Real.sin (Real.pi * (α r - α r')) : ℂ)‖ ≤
        (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  have he : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))) =
      (1 / (2 * Complex.I)) * ∑ r ∈ s, ∑ r' ∈ s.erase r,
        b r * (starRingEnd ℂ) (b r') /
          (Real.sin (Real.pi * (α r - α r')) : ℂ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    rw [mul_sum]
    apply sum_congr rfl
    intro r' hr'
    rw [circular_kernel_eq_cosecant]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hc : ‖(1 : ℂ) / (2 * Complex.I)‖ = 1 / 2 := by
    norm_num [norm_div, norm_mul]
  rw [he, norm_mul, hc]
  calc
    _ ≤ (1 / 2) * ((1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

/-- Gallagher 1975 p.131. Exact finite duality preserves the sharp constant.
CONDITIONAL ON the supplied circular Hilbert bound. -/
theorem spaced_sampling_of_hilbert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (hh : ∀ v : ι → ℂ,
      ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        v r * (starRingEnd ℂ) (v r') *
          (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
            (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
        (1 / (2 * δ)) * ∑ r ∈ s, ‖v r‖ ^ 2)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 ≤
      ((N : ℝ) + 1 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  apply LeanLab.RieselVaughan1983.LargeSieveSchur.primal_of_dual (by positivity) M N
  intro b
  change (∑ n ∈ Ioc M (M + N),
    ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2) ≤ _
  rw [fourier_energy_split]
  have hcard : (Ioc M (M + (N : ℤ))).card = N :=
    LeanLab.RieselVaughan1983.LargeSieveSchur.card_Ioc_eq M N
  rw [hcard]
  have hre : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      (b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re) ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [Complex.re_sum] using
      (Complex.re_le_norm _).trans (offdiagonal_bound_of_hilbert s α hδ hs hh b M N)
  calc
    _ ≤ (N : ℝ) * (∑ r ∈ s, ‖b r‖ ^ 2) + (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 :=
      add_le_add le_rfl hre
    _ = _ := by ring

/-- Gallagher 1975 p.131. Farey spacing turns the sharp dual constant into N plus Q squared.
CONDITIONAL ON the supplied circular Hilbert bound at the reduced fractions. -/
theorem farey_sampling_of_hilbert (a : ℕ → ℂ) (M N Q : ℕ)
    (hh : ∀ b : ℕ × ℕ → ℂ,
      ‖∑ r ∈ LeanLab.PNTPort.LargeSieve.farey Q,
        ∑ r' ∈ (LeanLab.PNTPort.LargeSieve.farey Q).erase r,
          b r * (starRingEnd ℂ) (b r') *
            (LeanLab.PNTPort.LargeSieve.e
                ((LeanLab.PNTPort.LargeSieve.fareyPt r - LeanLab.PNTPort.LargeSieve.fareyPt r') / 2) /
              (LeanLab.PNTPort.LargeSieve.e
                (LeanLab.PNTPort.LargeSieve.fareyPt r - LeanLab.PNTPort.LargeSieve.fareyPt r') - 1))‖ ≤
        (1 / (2 * (1 / (Q : ℝ) ^ 2))) *
          ∑ r ∈ LeanLab.PNTPort.LargeSieve.farey Q, ‖b r‖ ^ 2) :
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp only [show Icc 1 (0 : ℕ) = ∅ by decide, sum_empty,
      Nat.cast_zero, zero_pow, add_zero]
    positivity
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  have hI : Ioc (M : ℤ) ((M : ℤ) + N) = (Ioc M (M + N)).map emb := by
    ext z
    simp only [Finset.mem_Ioc, Finset.mem_map, emb, Function.Embedding.coeFn_mk, Int.ofNat_eq_natCast]
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨z.toNat, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
      constructor <;> omega
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hbound := spaced_sampling_of_hilbert
    (LeanLab.PNTPort.LargeSieve.farey Q) LeanLab.PNTPort.LargeSieve.fareyPt
    hδ (LeanLab.PNTPort.LargeSieve.farey_spaced Q)
    hh
    (fun z : ℤ => a z.toNat) (M : ℤ) N
  rw [hI] at hbound
  simp only [sum_map, emb, Function.Embedding.coeFn_mk,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast] at hbound
  have hconst : (1 : ℝ) / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by simp
  rw [hconst] at hbound
  rw [LeanLab.PNTPort.LargeSieve.farey_sum_eq] at hbound
  simpa only [LeanLab.PNTPort.LargeSieve.U, LeanLab.PNTPort.LargeSieve.fareyPt,
    Nat.coprime_comm] using hbound

/-- LEAF. Montgomery and Vaughan, Hilbert's inequality, 1974 pp.73 to 82.
The classical circular cosecant inequality for separated points is the remaining input.
The family size is at least four because smaller families are proved by the Schur estimate.
The quotient normalization, geometric endpoints, duality and Farey constant are separate.
This supplies the sharp sampling input behind Gallagher 1975 p.131 display 14. -/
theorem cosecant_hilbert_large_family {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ) (hcard : 4 ≤ s.card) (b : ι → ℂ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') /
        (Real.sin (Real.pi * (α r - α r')) : ℂ)‖ ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  exact LeanLab.Linnik.HilbertCosecant.cosecant_hilbert s α hδ hs b

/-- Gallagher 1975 p.131. The circular Hilbert bound is proved for small families and is
CONDITIONAL ON cosecant_hilbert_large_family for every larger family. -/
theorem circular_hilbert_sharp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ) (b : ι → ℂ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  by_cases hc : s.card ≤ 3
  · exact circular_hilbert_small_family s α hδ hs hc b
  · exact circular_hilbert_of_cosecant s α hδ b
      (cosecant_hilbert_large_family s α hδ hs (by omega) b)

/-- Gallagher 1975 p.131. The general separated sampling estimate now has no supplied
Hilbert hypothesis. The additive interval coefficient is N plus reciprocal delta. -/
theorem spaced_sampling {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 ≤
      ((N : ℝ) + 1 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  exact spaced_sampling_of_hilbert s α hδ hs
    (fun v => circular_hilbert_sharp s α hδ hs v) a M N

/-- LEAF. Montgomery 1971, Topics in multiplicative number theory, sharp additive large sieve.
Gallagher 1975 p.131, the input behind display 14. Only the sharp Fourier sampling bound
remains here. Primitive character orthogonality is proved separately. -/
theorem additive_large_sieve_sharp (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  apply farey_sampling_of_hilbert a M N Q
  intro b
  by_cases hQ : Q = 0
  · subst Q
    simp [LeanLab.PNTPort.LargeSieve.farey]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  exact circular_hilbert_sharp (LeanLab.PNTPort.LargeSieve.farey Q)
    LeanLab.PNTPort.LargeSieve.fareyPt hδ
    (LeanLab.PNTPort.LargeSieve.farey_spaced Q) b

/-- LEAF. Unit U-1532. The multiplicative large sieve over primitive characters,
`Σ_{q ≤ Q} q/φ(q) Σ*_χ |Σ_{M < n ≤ M+N} a_n χ(n)|² ≤ (N + Q²) Σ |a_n|²`, the input behind the
bound for `E` in display (14) p. 131 and behind the density estimate below. -/
theorem large_sieve (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  calc
    _ ≤ _ := primitive_sieve_le_additive a M N Q
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ Ioc M (M + N), ‖(starRingEnd ℂ) (a n)‖ ^ 2 :=
      additive_large_sieve_sharp (fun n => (starRingEnd ℂ) (a n)) M N Q
    _ = _ := by simp only [Complex.norm_conj]

/-- The logarithm in the existing zero free region is bounded uniformly in the paper box. -/
theorem log_Bt_le_log_height : ∃ K : ℝ, 0 < K ∧ ∀ {q : ℕ} [NeZero q] {T t : ℝ},
    2 ≤ T → (q : ℝ) ≤ T → |t| ≤ T → Real.log (Bt q t) ≤ K * Real.log T := by
  let A := Real.log (6 * Z)
  let K := A / Real.log 2 + 2
  have hZ := one_le_Z
  have hA : 0 ≤ A := Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro q _ T t hT hq ht
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hBt : Bt q t ≤ (6 * Z) * T ^ 2 := by
    unfold Bt
    have h1 := mul_le_mul hq (show |t| + 3 ≤ 3 * T by linarith) (by positivity) hT0.le
    nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ Z by linarith)]
  calc
    Real.log (Bt q t) ≤ Real.log ((6 * Z) * T ^ 2) :=
      Real.log_le_log (by unfold Bt; positivity) hBt
    _ = A + 2 * Real.log T := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num [A]
    _ ≤ K * Real.log T := by
      have hmul : A ≤ A / Real.log 2 * Real.log T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hlog hA
      dsimp [K]
      nlinarith

/-- The nonprincipal part of the exceptional zero reality assertion on p.127. -/
theorem height_box_real_nonprincipal : ∃ b : ℝ, 0 < b ∧ ∀ {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ {T : ℝ}, 2 ≤ T → (q : ℝ) ≤ T →
    ∀ ρ : ℂ, χ.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      χ ^ 2 = 1 ∧ ρ.im = 0 := by
  obtain ⟨K, hK, hlog⟩ := log_Bt_le_log_height
  obtain ⟨c, c', hc, hc', hreg⟩ := zero_free_region_real
  refine ⟨c / (2 * K), by positivity, ?_⟩
  intro q _ χ hχ T hT hq ρ hz hβ ht
  rcases (hreg q χ hχ).1 ρ hz with hleft | hright
  · have hlT : 0 < Real.log T := Real.log_pos (by linarith)
    have hlB : 0 < Real.log (Bt q ρ.im) := by linarith [one_le_log_Bt (N := q) ρ.im]
    have hd : c / (K * Real.log T) ≤ c / Real.log (Bt q ρ.im) :=
      div_le_div_of_nonneg_left hc.le hlB (hlog hT hq ht)
    have hpos : 0 < c / (2 * K) / Real.log T := by positivity
    have heq : c / (K * Real.log T) = 2 * (c / (2 * K) / Real.log T) := by field_simp
    rw [heq] at hd
    linarith
  · exact ⟨hright.2.2.1, hright.2.2.2⟩

/-- The principal primitive character has no zero in a uniform p.127 box. -/
theorem zeta_height_box_nonzero : ∃ b : ℝ, 0 < b ∧ ∀ {T : ℝ}, 2 ≤ T →
    ∀ ρ : ℂ, 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T → riemannZeta ρ ≠ 0 := by
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  obtain ⟨σ, hσ, hsmall⟩ := ZetaNoZerosInBox 3
  let b := min A ((1 - σ) * Real.log 2)
  have hb : 0 < b := lt_min hA.1 (mul_pos (by linarith) (Real.log_pos (by norm_num)))
  refine ⟨b, hb, ?_⟩
  intro T hT ρ hβ ht
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hrep : (ρ.re : ℂ) + ρ.im * Complex.I = ρ := by simp
  by_cases h1 : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  by_cases ht3 : |ρ.im| ≤ 3
  · have hcmp : b / Real.log T ≤ 1 - σ := by
      apply (div_le_iff₀ hlT).mpr
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
      have hmin : b ≤ (1 - σ) * Real.log 2 := min_le_right _ _
      nlinarith
    simpa only [hrep] using hsmall ρ.im ht3 ρ.re (by linarith)
  · have ht3' : 3 < |ρ.im| := lt_of_not_ge ht3
    have hlogt : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
    have hcomp : b / Real.log T ≤ A / Real.log |ρ.im| := by
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hlT.le).trans
        (div_le_div_of_nonneg_left hA.1.le hlogt (Real.log_le_log (by positivity) ht))
    have hh := hlarge ρ.re ρ.im ht3' ⟨by simpa only [Real.rpow_one] using (show 1 - A / Real.log |ρ.im| ≤ ρ.re by linarith), lt_of_not_ge h1⟩
    simpa only [hrep] using hh

/-- Equality of primitive characters follows from equality at a common multiple. -/
theorem primitive_sigma_eq_of_lift_eq {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ (q₁ + 1)) (χ₂ : DirichletCharacter ℂ (q₂ + 1))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (he : DirichletCharacter.changeLevel (Nat.dvd_mul_right (q₁ + 1) (q₂ + 1)) χ₁ =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left (q₂ + 1) (q₁ + 1)) χ₂) :
    (⟨q₁, χ₁⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q₂, χ₂⟩ := by
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    h₁, h₂] at hc
  have hq : q₁ = q₂ := by omega
  subst q₂
  have hχ := DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right (q₁ + 1) (q₁ + 1)) he
  subst χ₂
  rfl

/-- Narrowing the zero strip preserves membership in the exceptional family. -/
theorem excSet_mono {b₁ b₂ T : ℝ} (hb : b₁ ≤ b₂) (hT : 2 ≤ T) :
    excSet b₁ T ⊆ excSet b₂ T := by
  rintro x ⟨hq, hp, ρ, hz, hβ, ht⟩
  refine ⟨hq, hp, ρ, hz, ?_, ht⟩
  have hdiv := div_le_div_of_nonneg_right hb (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
  linarith

/-- No primitive principal character occurs in the uniform zero strip on p.127. -/
theorem excSet_nonprincipal : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ x ∈ excSet b T, x.2 ≠ 1 := by
  obtain ⟨b, hb, hz⟩ := zeta_height_box_nonzero
  refine ⟨b, hb, ?_⟩
  intro T hT x hx he
  have hc := hx.2.1
  rw [DirichletCharacter.IsPrimitive, he, DirichletCharacter.conductor_one] at hc
  have hq : x.1 = 0 := by omega
  obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
  have hzeta : riemannZeta ρ = 0 := by
    rcases x with ⟨q, χ⟩
    dsimp at hq
    subst q
    simpa only [he, DirichletCharacter.LFunction_modOne_eq] using hρ
  exact hz hT ρ hβ ht hzeta


/-- LEAF. Unit U-1532. The exceptional zero is real and its character is real, p. 127: for
small `b > 0`, any zero in `Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T` of `L(s, χ)`, `χ` primitive of
conductor at most `T`, has `Im ρ = 0`, and `χ² = 1`. -/
theorem page_real : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    x.2 ^ 2 = 1 ∧ ∀ ρ : ℂ, x.2.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      ρ.im = 0 := by
  obtain ⟨bn, hbn, hn⟩ := height_box_real_nonprincipal
  obtain ⟨bz, hbz, hz⟩ := zeta_height_box_nonzero
  let b := min bn bz
  refine ⟨b, lt_min hbn hbz, ?_⟩
  intro T hT x hx
  have hq : ((x.1 + 1 : ℕ) : ℝ) ≤ T := by simpa using hx.1
  have hprim := hx.2.1
  have hχ : x.2 ≠ 1 := by
    intro he
    have hlev : x.1 + 1 = 1 := by
      have hc := hprim
      rw [DirichletCharacter.IsPrimitive, he, DirichletCharacter.conductor_one] at hc
      exact hc.symm
    obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
    have hzeta : riemannZeta ρ = 0 := by
      have hxp : x.1 = 0 := by omega
      rcases x with ⟨q, χ⟩
      dsimp at hxp
      subst q
      simpa only [he, DirichletCharacter.LFunction_modOne_eq] using hρ
    have hβz : 1 - bz / Real.log T ≤ ρ.re := by
      have hcmp := div_le_div_of_nonneg_right (min_le_right bn bz) (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
      linarith
    exact hz hT ρ hβz ht hzeta
  have hmono (ρ : ℂ) (hβ : 1 - b / Real.log T ≤ ρ.re) : 1 - bn / Real.log T ≤ ρ.re := by
    have hcmp := div_le_div_of_nonneg_right (min_le_left bn bz) (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
  refine ⟨(hn x.2 hχ hT hq ρ hρ (hmono ρ hβ) ht).1, ?_⟩
  intro ρ hρ hβ ht
  exact (hn x.2 hχ hT hq ρ hρ (hmono ρ hβ) ht).2

/-- The finite Fourier identity before the order split in Lemma 6 on pp.134 and 135. -/
theorem ramanujan_tuple_sum_eq (q k L : ℕ) :
    ∑ x : pairs k L, ramanujanSum q (dif x) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ((‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) : ℝ) : ℂ) := by
  classical
  unfold ramanujanSum
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  have hp : Gs L ((a : ℝ) / q) ^ k =
      ∑ ν : Fin k → Fin L, eC (sv ν * ((a : ℝ) / q)) :=
    LeanLab.Linnik.U1434Lemma21.Gs_pow k L _
  have hc (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
    simpa only [LeanLab.Linnik.U1434Lemma21.e_eq_eC] using
      (LeanLab.PNTPort.LargeSieve.e_neg x).symm
  have hn : ((‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) : ℝ) : ℂ) =
      Gs L ((a : ℝ) / q) ^ k * (starRingEnd ℂ) (Gs L ((a : ℝ) / q) ^ k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  rw [hn, hp, map_sum, sum_mul_sum, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro ν hν
  apply sum_congr rfl
  intro mu hmu
  rw [hc, ← LeanLab.Linnik.U1434Lemma21.eC_add]
  congr 1
  simp only [dif, Int.cast_sub, Int.cast_natCast]
  ring

/-- The q one main term in the finite expansion of Lemma 6. -/
theorem ramanujan_tuple_sum_one (k L : ℕ) :
    ∑ x : pairs k L, ramanujanSum 1 (dif x) = (L : ℂ) ^ (2 * k) := by
  have hR (n : ℤ) : ramanujanSum 1 n = 1 := by simp [ramanujanSum, eC]
  simp only [hR, sum_const, nsmul_eq_mul, mul_one]
  simp [pairs, Fintype.card_prod, ← pow_add, two_mul]

/-- The justified finite sum and singular series exchange at the start of Lemma 6. -/
theorem offdiag_singSeries_eq_tsum (k L : ℕ) :
    ∑ x : pairs k L with dif x ≠ 0, singSeries (dif x) =
      ∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x ≠ 0, ramanujanSum q (dif x) := by
  classical
  have hs : ∀ x ∈ (univ : Finset (pairs k L)).filter (fun x => dif x ≠ 0),
      Summable (fun q : ℕ => ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 /
        (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x)) := by
    intro x hx
    exact summable_singSeries (mem_filter.mp hx).2
  simp only [singSeries]
  rw [← Summable.tsum_finsetSum hs]
  apply tsum_congr
  intro q
  exact (mul_sum _ _ _).symm

/-- The zero frequency Ramanujan coefficient removed on p.134. -/
theorem ramanujanSum_zero (q : ℕ) : ramanujanSum q 0 = (q.totient : ℂ) := by
  simp [ramanujanSum, eC, Nat.totient, Nat.coprime_comm]

/-- The square root order series used in Lemma 10 on p.137 is uniformly bounded. -/
theorem half_order_totient_weight_le (S : Finset ℕ) :
    ∑ q ∈ S with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q)) ≤ 16 * Real.log 2 * Real.exp 27 := by
  classical
  have hpoint (q : ℕ) (hq : q ∈ S.filter Odd) :
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q)) ≤ LeanLab.Romanov.halfOrderTerm q := by
    have ho := (mem_filter.mp hq).2
    by_cases hs : Squarefree q
    · rw [LeanLab.Romanov.halfOrderTerm, ite_eq_left (show LeanLab.LPZ2007.OddSqf q from ⟨ho, hs⟩)]
      rw [div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right
        (LeanLab.Romanov.TotientWeights134.totientWeight_le_fd ⟨ho, hs⟩) (Real.sqrt_nonneg _)
    · simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, Int.cast_zero,
        zero_pow (by decide : 2 ≠ 0), zero_div]
      exact LeanLab.Romanov.halfOrderTerm_nonneg q
  exact (sum_le_sum hpoint).trans
    ((LeanLab.Romanov.halfOrder_summable.sum_le_tsum _
      (fun q _ => LeanLab.Romanov.halfOrderTerm_nonneg q)).trans LeanLab.Romanov.halfOrder_tsum_le)

/-- The least common multiple order kernel in Lemma 10 on p.137 gains a square root order. -/
theorem lcm_order_weight_le {f : ℕ} (hf : Odd f) (S : Finset ℕ) :
    ∑ q ∈ S with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (q.totient : ℝ) / ordTwo (Nat.lcm f q) ≤
      (16 * Real.log 2 * Real.exp 27) / Real.sqrt (ordTwo f) := by
  classical
  have hfpos : (0 : ℝ) < ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have hsf : 0 < Real.sqrt (ordTwo f) := Real.sqrt_pos.mpr hfpos
  have hpoint (q : ℕ) (hq : q ∈ S.filter Odd) :
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) / ordTwo (Nat.lcm f q) ≤
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := by
    have hqo := (mem_filter.mp hq).2
    have hlo : Odd (Nat.lcm f q) :=
      (hf.mul hqo).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right f q) (dvd_mul_left q f))
    have hlpos : (0 : ℝ) < ordTwo (Nat.lcm f q) :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hlo
    have hqpos : (0 : ℝ) < ordTwo q :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hqo
    have hsqp : 0 < Real.sqrt (ordTwo q) := Real.sqrt_pos.mpr hqpos
    have hfle : (ordTwo f : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast LeanLab.Linnik.Decomp1537a.xi_le_of_dvd hlo (Nat.dvd_lcm_left f q)
    have hqle : (ordTwo q : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast LeanLab.Linnik.Decomp1537a.xi_le_of_dvd hlo (Nat.dvd_lcm_right f q)
    have hsqrt : Real.sqrt (ordTwo f) * Real.sqrt (ordTwo q) ≤ ordTwo (Nat.lcm f q) := by
      calc
        _ = Real.sqrt ((ordTwo f : ℝ) * ordTwo q) := (Real.sqrt_mul hfpos.le _).symm
        _ ≤ Real.sqrt ((ordTwo (Nat.lcm f q) : ℝ) * ordTwo (Nat.lcm f q)) :=
          Real.sqrt_le_sqrt (mul_le_mul hfle hqle hqpos.le hlpos.le)
        _ = _ := Real.sqrt_mul_self hlpos.le
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) by positivity)
      (mul_pos hsf hsqp) hsqrt
    convert hh using 1 <;> rw [div_mul_eq_div_div] <;> ring
  calc
    _ ≤ ∑ q ∈ S with Odd q,
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := sum_le_sum hpoint
    _ = (∑ q ∈ S with Odd q, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (half_order_totient_weight_le S) hsf.le

/-- The first divisor reduction of Lemma 10 on p.137 with an explicit factor eight. -/
theorem exceptional_gcd_totient_le {r s : ℕ} (hs : 0 < s)
    (hr : r = s ∨ r = 4 * s ∨ r = 8 * s) (n : ℕ) :
    (Nat.gcd r n).totient ≤ 8 * ∑ f ∈ (Nat.gcd s n).divisors, f.totient := by
  rw [Nat.sum_totient]
  have hg : 0 < Nat.gcd s n := Nat.gcd_pos_of_pos_left n hs
  have hbound (d : ℕ) (hd : 0 < d) : Nat.gcd (d * s) n ≤ d * Nat.gcd s n := by
    apply Nat.le_of_dvd (Nat.mul_pos hd hg)
    have hdiv : Nat.gcd (d * s) n ∣ Nat.gcd (d * s) (d * n) :=
      Nat.gcd_dvd_gcd_of_dvd_right (d * s) (dvd_mul_left n d)
    rwa [Nat.gcd_mul_left] at hdiv
  have hφ := Nat.totient_le (Nat.gcd r n)
  rcases hr with hr | hr | hr
  · subst r; omega
  · subst r; have hh := hbound 4 (by decide); omega
  · subst r; exact hφ.trans (hbound 8 (by decide))

/-- The direct Lemma 8 bound leaves a conductor factor and no logarithmic decay. -/
theorem twisted_totient_crude : ∃ C : ℝ, ∀ k N r : ℕ,
    1 ≤ k → k ≤ N → 2 ≤ N → 0 < r →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) *
        ((r : ℝ) * (Nat.gcd r (dif x).natAbs).totient / (r.totient : ℝ) ^ 2) ≤
      C * ((r : ℝ) / r.totient) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C, hC⟩ := LeanLab.Linnik.Decomp1532a.lemma8
  refine ⟨C, ?_⟩
  intro k N r hk hkN hN hr
  have hφ : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr
  have hfactor (n : ℕ) :
      (r : ℝ) * (Nat.gcd r n).totient / (r.totient : ℝ) ^ 2 ≤ (r : ℝ) / r.totient := by
    have hdiv := Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left r n)
    have hle : ((Nat.gcd r n).totient : ℝ) ≤ r.totient := by
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hr) hdiv
    calc
      _ ≤ (r : ℝ) * r.totient / (r.totient : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg r)) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
        ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) * ((r : ℝ) / r.totient) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hfactor _) (by positivity)
    _ = ((r : ℝ) / r.totient) *
        (∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
          ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ)) := by rw [← sum_mul]; ring
    _ ≤ ((r : ℝ) / r.totient) * (C * (Nat.log 2 N : ℝ) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left (hC k N hk hkN hN) (by positivity)
    _ = _ := by ring

/-- LEAF. Unit U-1532. Page's theorem, p. 127: there is `b > 0` such that for every `T ≥ 2` at
most one primitive character of conductor at most `T` has an L-function with a zero in
`Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`. -/
theorem page_subsingleton : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → (excSet b T).Subsingleton := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨cl, hcl, hl⟩ := landau
  let b := min (min br bn) cl
  have hbr' : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbn' : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hcl' : b ≤ cl := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) hcl, ?_⟩
  intro T hT x hx y hy
  have hxbr := excSet_mono hbr' hT hx
  have hybr := excSet_mono hbr' hT hy
  have hxne := hn T hT x (excSet_mono hbn' hT hx)
  have hyne := hn T hT y (excSet_mono hbn' hT hy)
  obtain ⟨ρ₁, hz₁, hb₁, ht₁⟩ := hx.2.2
  obtain ⟨ρ₂, hz₂, hb₂, ht₂⟩ := hy.2.2
  have hβbr₁ : 1 - br / Real.log T ≤ ρ₁.re := by
    have hd := div_le_div_of_nonneg_right hbr' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have hβbr₂ : 1 - br / Real.log T ≤ ρ₂.re := by
    have hd := div_le_div_of_nonneg_right hbr' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him₁ := (hr T hT x hxbr).2 ρ₁ hz₁ hβbr₁ ht₁
  have him₂ := (hr T hT y hybr).2 ρ₂ hz₂ hβbr₂ ht₂
  have he₁ : (ρ₁.re : ℂ) = ρ₁ := by apply Complex.ext <;> simp [him₁]
  have he₂ : (ρ₂.re : ℂ) = ρ₂ := by apply Complex.ext <;> simp [him₂]
  have hzreal₁ : x.2.LFunction (ρ₁.re : ℂ) = 0 := by rwa [he₁]
  have hzreal₂ : y.2.LFunction (ρ₂.re : ℂ) = 0 := by rwa [he₂]
  have hbtop₁ : ρ₁.re ≤ 1 := by
    by_contra hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re x.2 (Or.inl hxne) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz₁
  have hbtop₂ : ρ₂.re ≤ 1 := by
    by_contra hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re y.2 (Or.inl hyne) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz₂
  have hQ : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT)
  have hxQ : x.1 + 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hx.1)
  have hyQ : y.1 + 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hy.1)
  have hlogQ : 0 < Real.log (⌊T⌋₊ : ℝ) := Real.log_pos (by exact_mod_cast hQ)
  have hlogT : Real.log (⌊T⌋₊ : ℝ) ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊T⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hcmp : b / Real.log T ≤ cl / Real.log (⌊T⌋₊ : ℝ) :=
    (div_le_div_of_nonneg_right hcl' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)).trans
      (div_le_div_of_nonneg_left hcl.le hlogQ hlogT)
  have hlift := hl ⌊T⌋₊ hQ (x.1 + 1) (y.1 + 1) hxQ hyQ x.2 y.2 hxne hyne
    ρ₁.re ρ₂.re hbtop₁ hbtop₂ hzreal₁ hzreal₂ (by linarith) (by linarith)
  exact primitive_sigma_eq_of_lift_eq x.2 y.2 hx.2.1 hy.2.1 hlift


/-- LEAF. Unit U-1532. Siegel's theorem, p. 127: for each `ε > 0` there is `c > 0` such that a
real zero `β` of `L(s, χ)`, `χ` real primitive of conductor `r`, has `1 - β ≥ c r^{-ε}`. -/
theorem siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ (q + 1),
    χ.IsPrimitive → χ ^ 2 = 1 → ∀ β : ℝ, χ.LFunction β = 0 →
      β ≤ 1 - c * ((q : ℝ) + 1) ^ (-ε) := by
  intro ε hε
  obtain ⟨cs, hcs, hs⟩ := siegel_zero ε hε
  let c := min (cs * (8 : ℝ) ^ (-ε)) (1 / 2)
  have hc : 0 < c := lt_min (mul_pos hcs (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)
  refine ⟨c, hc, fun q χ hprim h2 β hz => ?_⟩
  by_cases hχ : χ = 1
  · have hlev : q + 1 = 1 := by
      have h := hprim
      rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at h
      exact h.symm
    have hq : q = 0 := by omega
    subst q
    have hzeta : riemannZeta (β : ℂ) = 0 := by rwa [DirichletCharacter.LFunction_modOne_eq] at hz
    have hβ : β ≤ 0 := by
      by_contra hh
      have hb0 : 0 < β := by linarith
      by_cases hb1 : 1 ≤ β
      · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hb1) hzeta
      · have hh := (riemannZeta_real_neg hb0 (by linarith)).2
        rw [hzeta] at hh
        norm_num at hh
    have hc2 : c ≤ 1 / 2 := min_le_right _ _
    norm_num
    linarith
  · have hb1 : β ≤ 1 := by
      by_contra hh
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz
    let M := 8 * (q + 1)
    have hM8 : 8 ≤ M := by dsimp [M]; omega
    haveI : NeZero M := ⟨by omega⟩
    have hd : q + 1 ∣ M := by exact ⟨8, by dsimp [M]; ring⟩
    have hz' : (DirichletCharacter.changeLevel hd χ).LFunction β = 0 := by
      rw [L_lift hd hχ, hz, zero_mul]
    have hbound := hs M hM8 (DirichletCharacter.changeLevel hd χ) (lift_ne_one hd hχ) (lift_sq hd h2) β hb1 hz'
    have hMr : (M : ℝ) = 8 * ((q : ℝ) + 1) := by dsimp [M]; push_cast; ring
    rw [hMr, Real.mul_rpow (by norm_num) (by positivity)] at hbound
    have hc' : c * ((q : ℝ) + 1) ^ (-ε) ≤ cs * ((8 : ℝ) ^ (-ε) * ((q : ℝ) + 1) ^ (-ε)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)
    linarith

/-- LEAF. Unit U-1532. Lemma 9, p. 136: the conductor `r` of a real primitive character is
`r₀`, `4r₀` or `8r₀` with `r₀` odd and squarefree. -/
theorem lemma9 {r : ℕ} (hr : 0 < r) (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) :
    ∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀) := by
  exact LeanLab.Romanov.Decomp134.lemma9 hr χ hχ h2

open LeanLab.Linnik.Decomp1537a
open LeanLab.Linnik.U1466Display17 (hval FD sv_cons)

/-- Gallagher 1975 p.137. The stronger squarefree product weight has the same square root order bound. -/
theorem kf_lcm_order_weight_le {f : ℕ} (hf : Odd f) (S : Finset ℕ) :
    ∑ q ∈ S, kf q / (ordTwo (Nat.lcm f q) : ℝ) ≤
      (16 * Real.log 2 * Real.exp 27) / Real.sqrt (ordTwo f) := by
  classical
  have hfpos : (0 : ℝ) < ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have hsf : 0 < Real.sqrt (ordTwo f) := Real.sqrt_pos.mpr hfpos
  have hpoint (q : ℕ) :
      kf q / (ordTwo (Nat.lcm f q) : ℝ) ≤
        LeanLab.Romanov.halfOrderTerm q / Real.sqrt (ordTwo f) := by
    by_cases hk : kf q = 0
    · rw [hk, zero_div]
      exact div_nonneg (LeanLab.Romanov.halfOrderTerm_nonneg q) hsf.le
    have hqo := odd_of_kf_ne hk
    have hqs : Squarefree q := by
      by_contra hs
      exact hk (by simp [kf, hs])
    have hlo : Odd (Nat.lcm f q) :=
      (hf.mul hqo).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right f q) (dvd_mul_left q f))
    have hlpos : (0 : ℝ) < ordTwo (Nat.lcm f q) :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hlo
    have hqpos : (0 : ℝ) < ordTwo q :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hqo
    have hsqp : 0 < Real.sqrt (ordTwo q) := Real.sqrt_pos.mpr hqpos
    have hfle : (ordTwo f : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast xi_le_of_dvd hlo (Nat.dvd_lcm_left f q)
    have hqle : (ordTwo q : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast xi_le_of_dvd hlo (Nat.dvd_lcm_right f q)
    have hsqrt : Real.sqrt (ordTwo f) * Real.sqrt (ordTwo q) ≤ ordTwo (Nat.lcm f q) := by
      calc
        _ = Real.sqrt ((ordTwo f : ℝ) * ordTwo q) := (Real.sqrt_mul hfpos.le _).symm
        _ ≤ Real.sqrt ((ordTwo (Nat.lcm f q) : ℝ) * ordTwo (Nat.lcm f q)) :=
          Real.sqrt_le_sqrt (mul_le_mul hfle hqle hqpos.le hlpos.le)
        _ = _ := Real.sqrt_mul_self hlpos.le
    have hfd : kf q = LeanLab.LPZ2007.fd q := by
      rw [kf, ite_eq_left ⟨hqo, hqs⟩, LeanLab.LPZ2007.Lemma61Port.fd_eq ⟨hqo, hqs⟩]
    rw [LeanLab.Romanov.halfOrderTerm, ite_eq_left (show LeanLab.LPZ2007.OddSqf q from ⟨hqo, hqs⟩)]
    rw [← hfd]
    change kf q / (ordTwo (Nat.lcm f q) : ℝ) ≤ kf q / Real.sqrt (ordTwo q) / Real.sqrt (ordTwo f)
    have hh := div_le_div_of_nonneg_left (kf_nonneg q) (mul_pos hsf hsqp) hsqrt
    calc
      _ ≤ kf q / (Real.sqrt (ordTwo f) * Real.sqrt (ordTwo q)) := hh
      _ = _ := by rw [div_mul_eq_div_div]; ring
  calc
    _ ≤ ∑ q ∈ S, LeanLab.Romanov.halfOrderTerm q / Real.sqrt (ordTwo f) :=
      sum_le_sum fun q _ => hpoint q
    _ = (∑ q ∈ S, LeanLab.Romanov.halfOrderTerm q) / Real.sqrt (ordTwo f) := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right
      ((LeanLab.Romanov.halfOrder_summable.sum_le_tsum S
        (fun q _ => LeanLab.Romanov.halfOrderTerm_nonneg q)).trans LeanLab.Romanov.halfOrder_tsum_le) hsf.le

/-- Gallagher 1975 p.137. A single weighted coordinate has a square root order main term and a logarithmic error. -/
theorem Aq_order_bound : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 2 ≤ L →
    ∀ f : ℕ, Odd f → ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
      Aq m f L ≤ (16 * Real.log 2 * Real.exp 27) * L / Real.sqrt (ordTwo f) + C * Real.log L := by
  classical
  obtain ⟨C, hC, hbound⟩ := sfac_Pm_le_log
  refine ⟨C, hC, fun L hL f hf m hm => ?_⟩
  have step1 : Aq m f L ≤
      ∑ d ∈ (Pm m L).divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d f)) + kf d) := by
    rw [Aq_eq_sum]
    apply sum_le_sum
    intro d _
    by_cases hk : kf d = 0
    · simp [hk]
    have hdodd := odd_of_kf_ne hk
    have hlo : Odd (Nat.lcm d f) :=
      (hdodd.mul hf).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right d f) (dvd_mul_left f d))
    have hc := card_nus_le m L hlo
    nlinarith [mul_le_mul_of_nonneg_left hc (kf_nonneg d)]
  have step2 : ∑ d ∈ (Pm m L).divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d f)) + kf d) =
      (L : ℝ) * ∑ d ∈ (Pm m L).divisors, kf d / xi (Nat.lcm d f) +
        sfac (Pm m L : ℤ) := by
    have he : sfac (Pm m L : ℤ) = ∑ d ∈ (Pm m L).divisors, kf d := by
      simpa using sfac_eq_sum_kf (Pm m L : ℤ) (by exact_mod_cast (Pm_pos m L).ne')
    rw [he, sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro d _
    ring
  have hs := kf_lcm_order_weight_le hf (Pm m L).divisors
  simp_rw [Nat.lcm_comm f] at hs
  change (∑ d ∈ (Pm m L).divisors, kf d / xi (Nat.lcm d f)) ≤ _ at hs
  calc
    _ ≤ _ := step1
    _ = _ := step2
    _ ≤ (L : ℝ) * ((16 * Real.log 2 * Real.exp 27) / Real.sqrt (ordTwo f)) + C * Real.log L :=
      add_le_add (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg L)) (hbound L hL m hm)
    _ = _ := by ring

/-- Gallagher 1975 p.137. Splitting the divisor sum at the fourth root gives square root logarithmic decay. -/
theorem divisor_sqrt_log_sum_le {s : ℕ} (hs : 0 < s) :
    ∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f) ≤
      3 * s / Real.sqrt (1 + Real.log s) := by
  classical
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlogs : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs1
  let t : ℝ := Real.sqrt (Real.sqrt s)
  let D := Real.sqrt (1 + Real.log s)
  have hD : 0 < D := Real.sqrt_pos.mpr (by linarith)
  have ht1 : 1 ≤ t := by
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hs1)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht2 : t * t = Real.sqrt s := by simp [pow_two, t]
  have hlogt : Real.log t = Real.log s / 4 := by
    dsimp [t]
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hsR.le]
    ring
  let A : Finset ℕ := s.divisors.filter (fun f : ℕ => (f : ℝ) ≤ t)
  let B : Finset ℕ := s.divisors.filter (fun f : ℕ => ¬ (f : ℝ) ≤ t)
  have hlocal (f : ℕ) (hf : f ∈ s.divisors) : 1 ≤ Real.sqrt (1 + Real.log f) := by
    have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Nat.pos_of_mem_divisors hf
    exact Real.one_le_sqrt.mpr (by linarith [Real.log_nonneg hf1])
  have hcard : (A.card : ℝ) ≤ t := by
    have hsub : A ⊆ Icc 1 ⌊t⌋₊ := by
      intro f hf
      obtain ⟨hfd, hft⟩ := mem_filter.mp hf
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hfd, Nat.le_floor hft⟩
    have hc := card_le_card hsub
    have hc' : A.card ≤ ⌊t⌋₊ := by simpa using hc
    exact (by exact_mod_cast hc' : (A.card : ℝ) ≤ ⌊t⌋₊).trans (Nat.floor_le ht0)
  have hsmall : (∑ f ∈ A, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤ Real.sqrt s := by
    calc
      _ ≤ ∑ _f ∈ A, t := by
        apply sum_le_sum
        intro f hf
        have hfd := (mem_filter.mp hf).1
        have ht := (mem_filter.mp hf).2
        calc
          _ ≤ (f.totient : ℝ) := div_le_self (Nat.cast_nonneg _) (hlocal f hfd)
          _ ≤ (f : ℝ) := by exact_mod_cast Nat.totient_le f
          _ ≤ t := ht
      _ = (A.card : ℝ) * t := by simp
      _ ≤ t * t := mul_le_mul_of_nonneg_right hcard ht0
      _ = _ := ht2
  have hpoint (f : ℕ) (hf : f ∈ B) :
      (f.totient : ℝ) / Real.sqrt (1 + Real.log f) ≤ (f.totient : ℝ) * (2 / D) := by
    have hfd := (mem_filter.mp hf).1
    have hft : t < (f : ℝ) := lt_of_not_ge (mem_filter.mp hf).2
    have hfpos : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_mem_divisors hfd
    have hlf : Real.log s / 4 ≤ Real.log f := by
      rw [← hlogt]
      exact Real.log_le_log (by linarith) hft.le
    have hlf0 : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg (by linarith)
    have hd : D ≤ 2 * Real.sqrt (1 + Real.log f) := by
      have hsqD : D ^ 2 = 1 + Real.log s := Real.sq_sqrt (by linarith)
      have hsqf := Real.sq_sqrt (show 0 ≤ 1 + Real.log (f : ℝ) by linarith)
      nlinarith [Real.sqrt_nonneg (1 + Real.log (f : ℝ))]
    have hfp : 0 < Real.sqrt (1 + Real.log (f : ℝ)) := by linarith [hlocal f hfd]
    rw [← mul_div_assoc, div_le_div_iff₀ hfp hD]
    nlinarith [show (0 : ℝ) ≤ f.totient from Nat.cast_nonneg _]
  have hlarge : (∑ f ∈ B, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤ (s : ℝ) * (2 / D) := by
    calc
      _ ≤ ∑ f ∈ B, (f.totient : ℝ) * (2 / D) := sum_le_sum hpoint
      _ = (∑ f ∈ B, (f.totient : ℝ)) * (2 / D) := (sum_mul _ _ _).symm
      _ ≤ (∑ f ∈ s.divisors, (f.totient : ℝ)) * (2 / D) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = (s : ℝ) * (2 / D) := by norm_cast; rw [Nat.sum_totient]
  have hroot : Real.sqrt s ≤ (s : ℝ) / D := by
    have hDle : D ≤ Real.sqrt s := by
      apply Real.sqrt_le_sqrt
      linarith [Real.log_le_sub_one_of_pos hsR]
    rw [le_div_iff₀ hD]
    calc
      Real.sqrt s * D ≤ Real.sqrt s * Real.sqrt s :=
        mul_le_mul_of_nonneg_left hDle (Real.sqrt_nonneg _)
      _ = s := by rw [← pow_two, Real.sq_sqrt hsR.le]
  have he := sum_filter_add_sum_filter_not s.divisors (fun f : ℕ => (f : ℝ) ≤ t)
    (fun f : ℕ => (f.totient : ℝ) / Real.sqrt (1 + Real.log f))
  change (∑ f ∈ A, _) + (∑ f ∈ B, _) = _ at he
  rw [← he]
  change _ ≤ 3 * s / D
  calc
    _ ≤ (s : ℝ) / D + (s : ℝ) * (2 / D) := add_le_add (hsmall.trans hroot) hlarge
    _ = _ := by ring

/-- Gallagher 1975 p.137. Two powers of log log are absorbed by one sixth power of log. -/
theorem log_sq_div_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 / Real.sqrt (1 + x) ≤ 144 / x ^ (1 / 3 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 12)
  have hsq : Real.log x ^ 2 ≤ 144 * x ^ (1 / 6 : ℝ) := by
    calc
      _ ≤ (12 * x ^ (1 / 12 : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ hlog0
        linarith
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 12 : ℝ)) 2, ← Real.rpow_mul hx0.le]
        norm_num
  have hmul : x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ) = Real.sqrt x := by
    rw [← Real.rpow_add hx0]
    norm_num
    exact (Real.sqrt_eq_rpow x).symm
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by linarith)) (Real.rpow_pos_of_pos hx0 _)]
  calc
    _ ≤ (144 * x ^ (1 / 6 : ℝ)) * x ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hx0.le _)
    _ = 144 * Real.sqrt x := by rw [mul_assoc, hmul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)

/-- Gallagher 1975 p.137. The totient ratio leaves a one third logarithmic power after the square root decay. -/
theorem totient_ratio_sqrt_log_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 3 ≤ r →
    ((r : ℝ) / r.totient) ^ 2 / Real.sqrt (1 + Real.log r) ≤
      C / Real.log r ^ (1 / 3 : ℝ) := by
  obtain ⟨A, hA⟩ := LeanLab.Linnik.Decomp1532a.div_totient_le_loglog
  let B := max A 0
  refine ⟨144 * B ^ 2, by positivity, fun r hr => ?_⟩
  have hl : 1 ≤ Real.log (r : ℝ) := by
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    apply le_of_lt
    rw [Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < r)]
    linarith [Real.exp_one_lt_d9]
  have hll : 0 ≤ Real.log (Real.log r) := Real.log_nonneg hl
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / r.totient := by positivity
  have hb : (r : ℝ) / r.totient ≤ B * Real.log (Real.log r) :=
    (hA r hr).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hll)
  have hb2 : ((r : ℝ) / r.totient) ^ 2 ≤ B ^ 2 * Real.log (Real.log r) ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left₀ hr0 hb 2
  calc
    _ ≤ (B ^ 2 * Real.log (Real.log r) ^ 2) / Real.sqrt (1 + Real.log r) :=
      div_le_div_of_nonneg_right hb2 (Real.sqrt_nonneg _)
    _ = B ^ 2 * (Real.log (Real.log r) ^ 2 / Real.sqrt (1 + Real.log r)) := by ring
    _ ≤ B ^ 2 * (144 / Real.log r ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (log_sq_div_sqrt_le hl) (sq_nonneg _)
    _ = _ := by ring

/-- Gallagher 1975 p.137. The conductor divisor split has the final uniform logarithmic decay. -/
theorem exceptional_divisor_log_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ r s : ℕ,
    3 ≤ r → 0 < s → (r = s ∨ r = 4 * s ∨ r = 8 * s) →
    (r : ℝ) / (r.totient : ℝ) ^ 2 *
      (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤
      C / Real.log r ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := totient_ratio_sqrt_log_decay
  refine ⟨6 * C, by positivity, fun r s hr hs hrs => ?_⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hφ : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  have hsr : s ≤ r := by rcases hrs with h | h | h <;> omega
  have hrs8 : r ≤ 8 * s := by rcases hrs with h | h | h <;> omega
  have hlogs : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs1
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hlog8 : Real.log (8 : ℝ) ≤ 3 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlog : Real.log (r : ℝ) ≤ 3 + Real.log s := by
    have hh := Real.log_le_log hr0 (show (r : ℝ) ≤ 8 * s by exact_mod_cast hrs8)
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hs0.ne'] at hh
    linarith
  have hDr : 0 < Real.sqrt (1 + Real.log (r : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hDs : 0 < Real.sqrt (1 + Real.log (s : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hcomp : Real.sqrt (1 + Real.log (r : ℝ)) ≤ 2 * Real.sqrt (1 + Real.log (s : ℝ)) := by
    have h1 := Real.sq_sqrt (show 0 ≤ 1 + Real.log (r : ℝ) by linarith)
    have h2 := Real.sq_sqrt (show 0 ≤ 1 + Real.log (s : ℝ) by linarith)
    nlinarith
  have hsum : (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) ≤
      6 * r / Real.sqrt (1 + Real.log r) := by
    calc
      _ ≤ 3 * s / Real.sqrt (1 + Real.log s) := divisor_sqrt_log_sum_le hs
      _ ≤ 6 * s / Real.sqrt (1 + Real.log r) := by
        rw [div_le_div_iff₀ hDs hDr]
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hsr : (s : ℝ) ≤ r) (by norm_num)) hDr.le
  calc
    _ ≤ (r : ℝ) / (r.totient : ℝ) ^ 2 * (6 * r / Real.sqrt (1 + Real.log r)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 6 * (((r : ℝ) / r.totient) ^ 2 / Real.sqrt (1 + Real.log r)) := by ring
    _ ≤ 6 * (C / Real.log r ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound r hr) (by norm_num)
    _ = _ := by ring

/-- Gallagher 1975 p.137. A restricted free exponent has an explicit square root order term and logarithmic error. -/
theorem one_coordinate_totient_order : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L →
    ∀ f : ℕ, Odd f → ∀ m : ℤ, |m| ≤ 2 ^ (2 * L + 2) →
      ∑ x : Fin L with hval m (Fin.val x) ≠ 0 ∧ (f : ℤ) ∣ hval m (Fin.val x),
        ((hval m (Fin.val x)).natAbs : ℝ) / (hval m (Fin.val x)).natAbs.totient ≤
      2 * (16 * Real.log 2 * Real.exp 27) * (L + 1) / Real.sqrt (ordTwo f) +
        2 * C * Real.log (L + 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := Aq_order_bound
  refine ⟨C, hC, fun L hL f hf m hm => ?_⟩
  let S : Finset (Fin L) := (univ : Finset (Fin L)).filter (fun x : Fin L => hval m (Fin.val x) ≠ 0 ∧ (f : ℤ) ∣ hval m (Fin.val x))
  have hsfac (h : ℤ) (hh : h ≠ 0) : FD 0 h = sfac h := by
    rw [sfac_eq_sum_kf h hh, FD, ite_eq_right hh]
    have he : h.natAbs.divisors.filter (fun d => 0 < d) = h.natAbs.divisors :=
      filter_eq_self.mpr fun d hd => Nat.pos_of_mem_divisors hd
    rw [he]
    rfl
  have hinj : Set.InjOn (fun x : Fin L => (x : ℕ) + 1) (S : Set (Fin L)) := by
    intro x hx y hy hxy
    apply Fin.ext
    change (x : ℕ) + 1 = (y : ℕ) + 1 at hxy
    omega
  have hsub : S.image (fun x : Fin L => (x : ℕ) + 1) ⊆ nus m f (L + 1) := by
    intro ν hν
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hν
    have hx' := (mem_filter.mp hx).2
    have hsign : m - 2 ^ ((x : ℕ) + 1) = -(hval m (Fin.val x)) := by unfold hval; ring
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, by have := x.isLt; omega⟩, ?_, ?_⟩
    · rw [hsign, neg_ne_zero]
      exact hx'.1
    · rw [hsign]
      exact dvd_neg.mpr hx'.2
  have heq : (∑ x ∈ S, sfac (hval m (Fin.val x))) =
      ∑ ν ∈ S.image (fun x : Fin L => (x : ℕ) + 1), sfac (m - 2 ^ ν) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro x hx
    have hsign : m - 2 ^ ((x : ℕ) + 1) = -(hval m (Fin.val x)) := by unfold hval; ring
    simp only [hsign, sfac, Int.natAbs_neg]
  have hA : ∑ x ∈ S, sfac (hval m (Fin.val x)) ≤ Aq m f (L + 1) := by
    rw [heq]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun ν _ _ => sfac_nonneg _)
  have hhm : |m| ≤ 2 ^ (2 * (L + 1)) := by convert hm using 1
  have hAb := hbound (L + 1) (by omega) f hf m hhm
  simp only [Nat.cast_add, Nat.cast_one] at hAb
  change (∑ x ∈ S, _) ≤ _
  calc
    _ ≤ ∑ x ∈ S, 2 * sfac (hval m (Fin.val x)) := by
      apply sum_le_sum
      intro x hx
      have hh := LeanLab.Linnik.Decomp1532a.totient_ratio_le_weight (hval m (Fin.val x))
      rwa [hsfac _ (mem_filter.mp hx).2.1] at hh
    _ = 2 * ∑ x ∈ S, sfac (hval m (Fin.val x)) := (mul_sum _ _ _).symm
    _ ≤ 2 * Aq m f (L + 1) := mul_le_mul_of_nonneg_left hA (by norm_num)
    _ ≤ 2 * ((16 * Real.log 2 * Real.exp 27) * (L + 1) / Real.sqrt (ordTwo f) +
        C * Real.log (L + 1)) := by exact mul_le_mul_of_nonneg_left hAb (by norm_num)
    _ = _ := by ring

/-- Gallagher 1975 p.137. The uniform weighted sum over multiples of an odd divisor has square root logarithmic decay. -/
theorem restricted_tuple_totient_bound : ∃ C : ℝ, 0 < C ∧ ∀ k N : ℕ,
    1 ≤ k → k ≤ N → 2 ≤ N → ∀ f : ℕ, Odd f → f ≤ N →
      ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0 ∧ (f : ℤ) ∣ dif x,
        ((dif x).natAbs : ℝ) / (dif x).natAbs.totient ≤
      C * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.sqrt (1 + Real.log f) := by
  classical
  obtain ⟨C, hC, hcoord⟩ := one_coordinate_totient_order
  let K : ℝ := 16 * Real.log 2 * Real.exp 27
  have hK : 0 < K := by dsimp [K]; positivity
  let A : ℝ := 2 * (K + C)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨12 * A, by positivity, fun k N hk hkN hN f hf hfN => ?_⟩
  let L := Nat.log 2 N
  have hL : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hNpow : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf.pos
  have hlf : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf1
  let D := Real.sqrt (1 + Real.log f)
  have hD : 0 < D := Real.sqrt_pos.mpr (by linarith)
  have ho : (0 : ℝ) < ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have ho1 : (1 : ℝ) ≤ ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have hDo : 1 + Real.log f ≤ 2 * ordTwo f := by
    have hh := LeanLab.Linnik.Decomp1532a.log_le_ordTwo_mul_log_two hf
    nlinarith
  have hDf : 1 + Real.log f ≤ 2 * ((L : ℝ) + 1) := by
    have hb : (f : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast hfN.trans hNpow.le
    have hh := Real.log_le_log (by linarith : (0 : ℝ) < f) hb
    rw [Real.log_pow] at hh
    push_cast at hh
    nlinarith
  have hcompO : D ≤ 2 * Real.sqrt (ordTwo f) := by
    have hsD : D ^ 2 = 1 + Real.log f := Real.sq_sqrt (by linarith)
    have hso := Real.sq_sqrt ho.le
    nlinarith [Real.sqrt_nonneg (ordTwo f)]
  have hcompL : D ≤ 2 * Real.sqrt ((L : ℝ) + 1) := by
    have hsD : D ^ 2 = 1 + Real.log f := Real.sq_sqrt (by linarith)
    have hsL := Real.sq_sqrt (show 0 ≤ (L : ℝ) + 1 by positivity)
    nlinarith [Real.sqrt_nonneg ((L : ℝ) + 1)]
  have hlogL : Real.log ((L : ℝ) + 1) ≤ 2 * Real.sqrt ((L : ℝ) + 1) := by
    have hh := Real.log_le_rpow_div (show 0 ≤ (L : ℝ) + 1 by positivity)
      (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hlogL0 : 0 ≤ Real.log ((L : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hshape : (((L : ℝ) + 1) / Real.sqrt (ordTwo f) + Real.log ((L : ℝ) + 1)) ≤
      12 * L / D := by
    have hmain : (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) * D ≤ 2 * ((L : ℝ) + 1) := by
      calc
        _ ≤ (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) * (2 * Real.sqrt (ordTwo f)) :=
          mul_le_mul_of_nonneg_left hcompO (by positivity)
        _ = _ := by field_simp
    have herr : Real.log ((L : ℝ) + 1) * D ≤ 4 * ((L : ℝ) + 1) := by
      calc
        _ ≤ (2 * Real.sqrt ((L : ℝ) + 1)) * (2 * Real.sqrt ((L : ℝ) + 1)) :=
          mul_le_mul hlogL hcompL hD.le (by positivity)
        _ = _ := by nlinarith [Real.sq_sqrt (show 0 ≤ (L : ℝ) + 1 by positivity)]
    rw [le_div_iff₀ hD]
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkey (ν : Fin j → Fin L) (mu : Fin (j + 1) → Fin L) :
      (∑ x : Fin L, if (f : ℤ) ∣ dif (Fin.cons x ν, mu) then
        ((dif (Fin.cons x ν, mu)).natAbs : ℝ) / (dif (Fin.cons x ν, mu)).natAbs.totient else 0) ≤
        (12 * A) * L / D := by
    let m : ℤ := (sv mu : ℤ) - sv ν
    have he (x : Fin L) : dif (Fin.cons x ν, mu) = hval m (Fin.val x) := by
      rw [dif, sv_cons]
      dsimp [hval, m]
      ring
    have hm : |m| ≤ 2 ^ (2 * L + 2) := by
      have hmu := LeanLab.Linnik.U1434Lemma21.sv_le mu
      have hν := LeanLab.Linnik.U1434Lemma21.sv_le ν
      have hmu' : sv mu ≤ N * 2 ^ L := hmu.trans (Nat.mul_le_mul_right _ hkN)
      have hν' : sv ν ≤ N * 2 ^ L := hν.trans (Nat.mul_le_mul_right _ (by omega))
      have hnat : m.natAbs ≤ N * 2 ^ L := by dsimp [m]; omega
      have hb : m.natAbs ≤ 2 ^ (2 * L + 2) := by
        calc
          _ ≤ N * 2 ^ L := hnat
          _ ≤ 2 ^ (L + 1) * 2 ^ L := Nat.mul_le_mul_right _ hNpow.le
          _ ≤ 2 ^ (2 * L + 2) := by rw [← pow_add]; apply Nat.pow_le_pow_right (by norm_num); omega
      rw [← Int.natCast_natAbs]
      exact_mod_cast hb
    have hco := hcoord L hL f hf m hm
    have heq : (∑ x : Fin L, if (f : ℤ) ∣ dif (Fin.cons x ν, mu) then
        ((dif (Fin.cons x ν, mu)).natAbs : ℝ) / (dif (Fin.cons x ν, mu)).natAbs.totient else 0) =
        ∑ x : Fin L with hval m (Fin.val x) ≠ 0 ∧ (f : ℤ) ∣ hval m (Fin.val x),
          ((hval m (Fin.val x)).natAbs : ℝ) / (hval m (Fin.val x)).natAbs.totient := by
      rw [sum_filter]
      apply sum_congr rfl
      intro x hx
      rw [he]
      by_cases hh : hval m (Fin.val x) = 0 <;> simp [hh]
    rw [heq]
    have hcoef : 2 * K * ((L : ℝ) + 1) / Real.sqrt (ordTwo f) + 2 * C * Real.log ((L : ℝ) + 1) ≤
        A * (((L : ℝ) + 1) / Real.sqrt (ordTwo f) + Real.log ((L : ℝ) + 1)) := by
      dsimp [A]
      have hu : 0 ≤ ((L : ℝ) + 1) / Real.sqrt (ordTwo f) := by positivity
      calc
        _ = (2 * K) * (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) + 2 * C * Real.log ((L : ℝ) + 1) := by ring
        _ ≤ (2 * (K + C)) * (((L : ℝ) + 1) / Real.sqrt (ordTwo f)) +
            (2 * (K + C)) * Real.log ((L : ℝ) + 1) :=
          add_le_add (mul_le_mul_of_nonneg_right (by linarith) hu)
            (mul_le_mul_of_nonneg_right (by linarith) hlogL0)
        _ = _ := by ring
    calc
      _ ≤ 2 * K * ((L : ℝ) + 1) / Real.sqrt (ordTwo f) + 2 * C * Real.log ((L : ℝ) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hco
      _ ≤ _ := hcoef
      _ ≤ A * (12 * L / D) := mul_le_mul_of_nonneg_left hshape hA.le
      _ = _ := by ring
  have heq : (∑ x : pairs (j + 1) L with dif x ≠ 0 ∧ (f : ℤ) ∣ dif x,
      ((dif x).natAbs : ℝ) / (dif x).natAbs.totient) =
      ∑ x : pairs (j + 1) L, if (f : ℤ) ∣ dif x then
        ((dif x).natAbs : ℝ) / (dif x).natAbs.totient else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    by_cases hh : dif x = 0 <;> simp [hh]
  change (∑ x : pairs (j + 1) L with _, _) ≤ _
  rw [heq, Fintype.sum_prod_type, LeanLab.Linnik.U1466Display17.sum_cons]
  calc
    _ = ∑ ν : Fin j → Fin L, ∑ mu : Fin (j + 1) → Fin L, ∑ x : Fin L,
        if (f : ℤ) ∣ dif (Fin.cons x ν, mu) then
          ((dif (Fin.cons x ν, mu)).natAbs : ℝ) / (dif (Fin.cons x ν, mu)).natAbs.totient else 0 := by
      exact sum_congr rfl (fun _ _ => sum_comm)
    _ ≤ ∑ _ν : Fin j → Fin L, ∑ _mu : Fin (j + 1) → Fin L, (12 * A) * L / D :=
      sum_le_sum (fun ν _ => sum_le_sum (fun mu _ => hkey ν mu))
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have he : 2 * (j + 1) = j + (j + 1) + 1 := by omega
      rw [he, pow_add, pow_add]
      ring

/-- Gallagher 1975 p.137. The exceptional gcd factor reduces to weighted sums over odd conductor divisors. -/
theorem weighted_gcd_divisor_reduction {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (n : ι → ℕ) (w : ι → ℝ) (hw : ∀ x ∈ T, 0 ≤ w x)
    {r s : ℕ} (hs : 0 < s) (hrs : r = s ∨ r = 4 * s ∨ r = 8 * s) :
    ∑ x ∈ T, w x * ((r : ℝ) * (Nat.gcd r (n x)).totient / (r.totient : ℝ) ^ 2) ≤
      (8 * r / (r.totient : ℝ) ^ 2) *
        ∑ f ∈ s.divisors, (f.totient : ℝ) * ∑ x ∈ T with f ∣ n x, w x := by
  classical
  have he (x : ι) : (Nat.gcd s (n x)).divisors = s.divisors.filter (fun f => f ∣ n x) := by
    ext f
    have hg := (Nat.gcd_pos_of_pos_left (n x) hs).ne'
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_left s (n x)), hs.ne'⟩, hd.trans (Nat.gcd_dvd_right s (n x))⟩
    · rintro ⟨⟨hfs, _⟩, hfn⟩
      exact ⟨Nat.dvd_gcd hfs hfn, hg⟩
  have hswap : (∑ x ∈ T, w x * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) =
      ∑ f ∈ s.divisors, (f.totient : ℝ) * ∑ x ∈ T with f ∣ n x, w x := by
    simp_rw [he, sum_filter, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro f hf
    apply sum_congr rfl
    intro x hx
    by_cases h : f ∣ n x <;> simp [h, mul_comm]
  calc
    _ = ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ∑ x ∈ T, w x * (Nat.gcd r (n x)).totient := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      ring
    _ ≤ ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ∑ x ∈ T, w x * (8 * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (hw x hx)
      exact_mod_cast exceptional_gcd_totient_le hs hrs (n x)
    _ = (8 * r / (r.totient : ℝ) ^ 2) *
        (∑ x ∈ T, w x * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) := by
      simp_rw [show ∀ x : ι, w x * (8 * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) =
        8 * (w x * ∑ f ∈ (Nat.gcd s (n x)).divisors, (f.totient : ℝ)) by intro x; ring]
      rw [← mul_sum]
      ring
    _ = _ := by rw [hswap]

/-- Gallagher 1975 pp.134 and 135. The odd reciprocal totient coefficient sum is logarithmic. -/
theorem reciprocal_totient_sum_le_log {R : ℕ} (hR : 2 ≤ R) :
    ∑ q ∈ Icc 1 R with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ≤
      Real.exp 24 * Real.log R := by
  classical
  calc
    _ ≤ ∑ q ∈ Icc 1 R with Odd q,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 := by
      apply sum_le_sum
      intro q hq
      have hqp : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqp
      have hle : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
      calc
        _ = ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q.totient / (q.totient : ℝ) ^ 2 := by
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) (sq_nonneg _)
    _ ≤ _ := LeanLab.Linnik.Decomp1532a.totient_square_sum_le_log hR

/-- Gallagher 1975 p.134. Restoring zero tuple differences in the truncated series costs a logarithmic diagonal error. -/
theorem truncated_ramanujan_diagonal_le {k : ℕ} (hk : 2 ≤ k) (L : ℕ) {R : ℕ} (hR : 2 ≤ R) :
    ‖∑ q ∈ Icc 1 R with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)‖ ≤
      2 * Real.exp 24 * (L : ℝ) ^ (2 * k - 2) * Real.log R := by
  classical
  let D := #{x : pairs k L | dif x = 0}
  let S := (Icc 1 R).filter Odd
  have hinner (q : ℕ) : (∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) =
      (D : ℂ) * q.totient := by
    calc
      _ = ∑ _x : pairs k L with dif _x = 0, (q.totient : ℂ) := by
        apply sum_congr rfl
        intro x hx
        rw [(mem_filter.mp hx).2, ramanujanSum_zero]
      _ = _ := by simp [D, nsmul_eq_mul]
  have hterm (q : ℕ) (hq : q ∈ S) :
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x) =
      (((D : ℝ) * (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
    have hqp : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hqp).ne'
    rw [hinner]
    push_cast
    field_simp
  have heq : (∑ q ∈ S,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) =
      (((D : ℝ) * (∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
    rw [sum_congr rfl hterm, ← Complex.ofReal_sum, ← mul_sum]
  have hsum0 : 0 ≤ ∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) := by positivity
  have hD : (D : ℝ) ≤ 2 * (L : ℝ) ^ (2 * k - 2) := by
    exact_mod_cast LeanLab.Linnik.Decomp1532a.rkk_zero_le hk L
  have hsum := reciprocal_totient_sum_le_log hR
  change ‖∑ q ∈ S, _‖ ≤ _
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg D) hsum0)]
  calc
    _ ≤ (2 * (L : ℝ) ^ (2 * k - 2)) * (Real.exp 24 * Real.log R) :=
      mul_le_mul hD hsum hsum0 (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 p.134. The reciprocal totient square tail has a uniform three fourths power saving. -/
theorem reciprocal_totient_square_tail (Q M : ℕ) (hQ : 0 < Q) :
    ∑ q ∈ Ioc Q M, (1 / (q.totient : ℝ) ^ 2) ≤
      (28 / 3 : ℝ) * (Q : ℝ) ^ (-(3 : ℝ) / 4) := by
  by_cases hQM : Q ≤ M
  · calc
      _ ≤ ∑ q ∈ Ioc Q M, 7 * (q : ℝ) ^ (-(7 : ℝ) / 4) := by
        apply sum_le_sum
        intro q hq
        exact LeanLab.Zinoviev1997.inv_totient_sq_seven q (by have := (mem_Ioc.mp hq).1; omega)
      _ = 7 * ∑ q ∈ Ioc Q M, (q : ℝ) ^ (-(7 : ℝ) / 4) := (mul_sum _ _ _).symm
      _ ≤ 7 * ((4 / 3 : ℝ) * (Q : ℝ) ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (LeanLab.Zinoviev1997.powerTail_Ioc Q M hQ hQM) (by norm_num)
      _ = _ := by ring
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity

/-- Gallagher 1975 p.134. A shifted cutoff form also covers the zero cutoff. -/
theorem reciprocal_totient_square_tail_succ (Q M : ℕ) :
    ∑ q ∈ Ioc Q M, (1 / (q.totient : ℝ) ^ 2) ≤
      64 * ((Q : ℝ) + 1) ^ (-(3 : ℝ) / 4) := by
  rcases Q with _ | Q
  · have hsub : Ioc 0 M ⊆ insert 1 (Ioc 1 M) := by
      intro q hq
      simp only [mem_Ioc, mem_insert] at hq ⊢
      omega
    have hh : (∑ q ∈ Ioc 0 M, (1 / (q.totient : ℝ) ^ 2)) ≤ 1 + 28 / 3 := by
      calc
        _ ≤ ∑ q ∈ insert 1 (Ioc 1 M), (1 / (q.totient : ℝ) ^ 2) :=
          sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
        _ = 1 + ∑ q ∈ Ioc 1 M, (1 / (q.totient : ℝ) ^ 2) := by rw [sum_insert (by simp)]; simp
        _ ≤ 1 + 28 / 3 := by simpa using add_le_add_left (reciprocal_totient_square_tail 1 M (by decide)) 1
    norm_num at hh ⊢
    linarith
  · have hpow : (((Q + 1 : ℕ) : ℝ) + 1) ^ (3 / 4 : ℝ) ≤
        2 * ((Q + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      calc
        _ ≤ (2 * ((Q + 1 : ℕ) : ℝ)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by push_cast; linarith) (by norm_num)
        _ = (2 : ℝ) ^ (3 / 4 : ℝ) * ((Q + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * ((Q + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    have hneg : ((Q + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) ≤
        2 * (((Q + 1 : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4) := by
      rw [show -(3 : ℝ) / 4 = -(3 / 4 : ℝ) by ring, Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      rw [← one_div, ← one_div, ← mul_div_assoc]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpow)
    have hh := reciprocal_totient_square_tail (Q + 1) M (by omega)
    calc
      _ ≤ (28 / 3 : ℝ) * ((Q + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 4) := hh
      _ ≤ (28 / 3 : ℝ) * (2 * (((Q + 1 : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hneg (by norm_num)
      _ ≤ _ := by push_cast; nlinarith [Real.rpow_nonneg (show 0 ≤ (Q : ℝ) + 1 + 1 by positivity) (-(3 : ℝ) / 4)]

/-- Gallagher 1975 p.134. The divisor weight in the power tail is uniformly bounded. -/
theorem three_fourths_div_totient_le {d : ℕ} (hd : 0 < d) :
    (d : ℝ) ^ (3 / 4 : ℝ) / d.totient ≤ 3 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hpow : ((d : ℝ) ^ (3 / 4 : ℝ)) ^ 8 = (d : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg d)]
    norm_num
  have hh : (d : ℝ) ^ 7 ≤ 2401 * (d.totient : ℝ) ^ 8 := by
    exact_mod_cast LeanLab.Zinoviev1997.seventh_le_totient_eighth d hd
  have hbound : (d : ℝ) ^ (3 / 4 : ℝ) ≤ 3 * d.totient := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (8 : ℕ) ≠ 0)).mp
    calc
      _ = (d : ℝ) ^ 6 := hpow
      _ ≤ (d : ℝ) ^ 7 := pow_le_pow_right₀ hdR (by decide)
      _ ≤ 2401 * (d.totient : ℝ) ^ 8 := hh
      _ ≤ _ := by rw [mul_pow]; norm_num; nlinarith [show (0 : ℝ) ≤ (d.totient : ℝ) ^ 8 by positivity]
  exact (div_le_iff₀ hφ).mpr hbound

/-- Gallagher 1975 p.134. The totient weight along multiples of one divisor has a uniform tail. -/
theorem totient_square_multiples_tail {d R : ℕ} (hd : 0 < d) (hR : 0 < R) (M : ℕ) :
    ∑ q ∈ (Ioc R M).filter (fun q => d ∣ q), (d.totient : ℝ) / (q.totient : ℝ) ^ 2 ≤
      192 / (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hdφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have heq : (∑ q ∈ (Ioc R M).filter (fun q => d ∣ q), (d.totient : ℝ) / (q.totient : ℝ) ^ 2) =
      ∑ j ∈ Ioc (R / d : ℕ) (M / d : ℕ), (d.totient : ℝ) / ((d * j).totient : ℝ) ^ 2 := by
    apply sum_bij (fun q _ => q / d)
    · intro q hq
      obtain ⟨hqI, hdq⟩ := mem_filter.mp hq
      obtain ⟨hRq, hqM⟩ := mem_Ioc.mp hqI
      refine mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hqM⟩
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa [Nat.div_mul_cancel hdq] using hRq
    · intro q hq q' hq' hqq
      have h1 := Nat.div_mul_cancel (mem_filter.mp hq).2
      have h2 := Nat.div_mul_cancel (mem_filter.mp hq').2
      rw [hqq] at h1
      omega
    · intro j hj
      obtain ⟨hRj, hjM⟩ := mem_Ioc.mp hj
      have hl : R < d * j := by simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hRj
      have hu : d * j ≤ M := by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hjM
      refine ⟨d * j, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hl, hu⟩, dvd_mul_right d j⟩, ?_⟩
      exact Nat.mul_div_cancel_left j hd
    · intro q hq
      rw [Nat.mul_div_cancel' (mem_filter.mp hq).2]
  have hpoint (j : ℕ) (hj : j ∈ Ioc (R / d : ℕ) (M / d : ℕ)) :
      (d.totient : ℝ) / ((d * j).totient : ℝ) ^ 2 ≤
        (1 / (d.totient : ℝ)) * (1 / (j.totient : ℝ) ^ 2) := by
    have hj0 : 0 < j := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hj).1
    have hjφ : (0 : ℝ) < j.totient := by exact_mod_cast Nat.totient_pos.mpr hj0
    have hmul : (d.totient : ℝ) * j.totient ≤ (d * j).totient := by
      exact_mod_cast Nat.totient_super_multiplicative d j
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg d.totient : (0 : ℝ) ≤ d.totient)
      (sq_pos_of_pos (mul_pos hdφ hjφ)) (pow_le_pow_left₀ (by positivity) hmul 2)
    calc
      _ ≤ (d.totient : ℝ) / ((d.totient : ℝ) * j.totient) ^ 2 := hh
      _ = _ := by field_simp
  have hcut : (R : ℝ) / d ≤ ((R / d : ℕ) : ℝ) + 1 := by
    have hn : R < (R / d + 1) * d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (R / d))
    apply (div_le_iff₀ hdR).mpr
    exact_mod_cast hn.le
  have hp : (((R / d : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4) ≤
      ((R : ℝ) / d) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hRR hdR) hcut (by norm_num)
  have hepow : ((R : ℝ) / d) ^ (-(3 : ℝ) / 4) =
      (d : ℝ) ^ (3 / 4 : ℝ) / (R : ℝ) ^ (3 / 4 : ℝ) := by
    rw [show -(3 : ℝ) / 4 = -(3 / 4 : ℝ) by ring, Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity), inv_div]
  calc
    _ = _ := heq
    _ ≤ ∑ j ∈ Ioc (R / d : ℕ) (M / d : ℕ), (1 / (d.totient : ℝ)) * (1 / (j.totient : ℝ) ^ 2) := sum_le_sum hpoint
    _ = (1 / (d.totient : ℝ)) * ∑ j ∈ Ioc (R / d : ℕ) (M / d : ℕ), (1 / (j.totient : ℝ) ^ 2) := (mul_sum _ _ _).symm
    _ ≤ (1 / (d.totient : ℝ)) * (64 * (((R / d : ℕ) : ℝ) + 1) ^ (-(3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (reciprocal_totient_square_tail_succ (R / d) (M / d)) (by positivity)
    _ ≤ (1 / (d.totient : ℝ)) * (64 * (((R : ℝ) / d) ^ (-(3 : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = (64 / (R : ℝ) ^ (3 / 4 : ℝ)) * ((d : ℝ) ^ (3 / 4 : ℝ) / d.totient) := by rw [hepow]; ring
    _ ≤ (64 / (R : ℝ) ^ (3 / 4 : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left (three_fourths_div_totient_le hd) (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 p.134. Expanding the gcd weight gives a uniform reciprocal totient square tail. -/
theorem gcd_totient_square_tail {n R : ℕ} (hn : 0 < n) (hR : 0 < R) (M : ℕ) :
    ∑ q ∈ Ioc R M, (Nat.gcd q n : ℝ) / (q.totient : ℝ) ^ 2 ≤
      192 * n.divisors.card / (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  have hdiv (q : ℕ) : (Nat.gcd q n).divisors = n.divisors.filter (fun d => d ∣ q) := by
    ext d
    have hg : Nat.gcd q n ≠ 0 := by
      simpa [Nat.gcd_comm] using (Nat.gcd_pos_of_pos_left q hn).ne'
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right q n), hn.ne'⟩, hd.trans (Nat.gcd_dvd_left q n)⟩
    · rintro ⟨⟨hdn, _⟩, hdq⟩
      exact ⟨Nat.dvd_gcd hdq hdn, hg⟩
  have hg (q : ℕ) : (Nat.gcd q n : ℝ) = ∑ d ∈ (Nat.gcd q n).divisors, (d.totient : ℝ) := by
    exact_mod_cast (Nat.sum_totient (Nat.gcd q n)).symm
  have heq : (∑ q ∈ Ioc R M, (Nat.gcd q n : ℝ) / (q.totient : ℝ) ^ 2) =
      ∑ d ∈ n.divisors, ∑ q ∈ (Ioc R M).filter (fun q => d ∣ q),
        (d.totient : ℝ) / (q.totient : ℝ) ^ 2 := by
    simp_rw [hg, hdiv, sum_filter, sum_div, ite_div, zero_div]
    rw [sum_comm]
  rw [heq]
  calc
    _ ≤ ∑ _d ∈ n.divisors, 192 / (R : ℝ) ^ (3 / 4 : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact totient_square_multiples_tail (Nat.pos_of_mem_divisors hd) hR M
    _ = _ := by simp; ring

/-- Gallagher 1975 p.134. Each singular series coefficient is bounded by its gcd majorant. -/
theorem singular_coefficient_norm_le_gcd {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n‖ ≤
      (Nat.gcd q n.natAbs : ℝ) / (q.totient : ℝ) ^ 2 := by
  by_cases hsf : Squarefree q
  · have hmu : ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    have hRc : ‖ramanujanSum q n‖ ≤ (Nat.gcd q n.natAbs : ℝ) := by
      rw [ramanujanSum_squarefree hsf n, norm_mul, Complex.norm_intCast, Complex.norm_natCast]
      have hm : |((ArithmeticFunction.moebius (q / Nat.gcd q n.natAbs) : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q / Nat.gcd q n.natAbs)
      calc
        _ ≤ ((Nat.gcd q n.natAbs).totient : ℝ) :=
          mul_le_of_le_one_left (Nat.cast_nonneg _) hm
        _ ≤ _ := by exact_mod_cast Nat.totient_le (Nat.gcd q n.natAbs)
    rw [hmu, one_div, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ ((q.totient : ℝ) ^ 2)⁻¹ * (Nat.gcd q n.natAbs : ℝ) :=
        mul_le_mul_of_nonneg_left hRc (by positivity)
      _ = _ := by ring
  · simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf, Int.cast_zero,
      zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, norm_zero]
    positivity

/-- Gallagher 1975 p.134. A uniform pointwise truncation error with an explicit power saving. -/
theorem singular_series_truncation_le {n : ℤ} (hn : n ≠ 0) {R : ℕ} (hR : 0 < R) :
    ‖singSeries n - ∑ q ∈ Icc 1 R,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n‖ ≤
      192 * n.natAbs.divisors.card / (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  let f : ℕ → ℂ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 /
    (q.totient : ℂ) ^ 2 * ramanujanSum q n
  have hs : Summable f := summable_singSeries hn
  have hf0 : f 0 = 0 := by simp [f]
  have htrunc : (∑ q ∈ range (R + 1), f q) = ∑ q ∈ Icc 1 R, f q := by
    have he : range (R + 1) = insert 0 (Icc 1 R) := by ext q; simp; omega
    rw [he, sum_insert (by simp), hf0, zero_add]
  have hlim : Tendsto (fun M : ℕ => ∑ q ∈ range M, f q) atTop (nhds (singSeries n)) :=
    hs.hasSum.tendsto_sum_nat
  have hnorm := (hlim.sub (tendsto_const_nhds (x := ∑ q ∈ range (R + 1), f q))).norm
  have hbound : ∀ᶠ M : ℕ in atTop, ‖(∑ q ∈ range M, f q) - ∑ q ∈ range (R + 1), f q‖ ≤
      192 * n.natAbs.divisors.card / (R : ℝ) ^ (3 / 4 : ℝ) := by
    filter_upwards [eventually_ge_atTop (R + 1)] with M hM
    have he : Ico (R + 1) M = Ioc R (M - 1) := by ext q; simp; omega
    rw [← sum_Ico_eq_sub f hM, he]
    calc
      _ ≤ ∑ q ∈ Ioc R (M - 1), ‖f q‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Ioc R (M - 1), (Nat.gcd q n.natAbs : ℝ) / (q.totient : ℝ) ^ 2 := by
        apply sum_le_sum
        intro q hq
        exact singular_coefficient_norm_le_gcd (by have := (mem_Ioc.mp hq).1; omega) n
      _ ≤ _ := gcd_totient_square_tail (Int.natAbs_pos.mpr hn) hR (M - 1)
  have hh := le_of_tendsto hnorm hbound
  rw [htrunc] at hh
  exact hh

/-- Gallagher 1975 p.134. The moving tuple average has a uniform truncation error at every reciprocal integer power. -/
theorem tuple_singular_truncation_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ k N R : ℕ, 2 ≤ N → 0 < R →
      ‖(∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x)) -
          ∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
            ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)‖ ≤
      C * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) * (Nat.log 2 N : ℝ) ^ (2 * k) /
        (R : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  obtain ⟨A, hA, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow m hm
  refine ⟨192 * A, by positivity, fun k N R hN hR => ?_⟩
  let L := Nat.log 2 N
  let T : Finset (pairs k L) := univ.filter (fun x => dif x ≠ 0)
  have hNpow : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hsize (x : pairs k L) : (dif x).natAbs ≤ k * N := by
    have hν := (LeanLab.Linnik.U1434Lemma21.sv_le x.1).trans (Nat.mul_le_mul_left k hNpow)
    have hμ := (LeanLab.Linnik.U1434Lemma21.sv_le x.2).trans (Nat.mul_le_mul_left k hNpow)
    dsimp [dif]
    omega
  have hpoint (x : pairs k L) (hx : x ∈ T) :
      ‖singSeries (dif x) - ∑ q ∈ Icc 1 R,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x)‖ ≤
      (192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ) := by
    have hn := (mem_filter.mp hx).2
    have hnpos := Int.natAbs_pos.mpr hn
    have hc := hτ (dif x).natAbs (by omega)
    have hmon : ((dif x).natAbs : ℝ) ^ ((m : ℝ)⁻¹) ≤ ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsize x) (by positivity)
    have hd := hc.trans (mul_le_mul_of_nonneg_left hmon hA.le)
    exact (singular_series_truncation_le hn hR).trans
      (by apply div_le_div_of_nonneg_right _ (by positivity); nlinarith)
  have hcard : (T.card : ℝ) ≤ (L : ℝ) ^ (2 * k) := by
    calc
      _ ≤ (Fintype.card (pairs k L) : ℝ) := by
        have hc : T.card ≤ (univ : Finset (pairs k L)).card := card_filter_le _ _
        exact_mod_cast hc
      _ = _ := by simp [pairs, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add, two_mul]
  have hswap : (∑ q ∈ Icc 1 R,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x ∈ T, ramanujanSum q (dif x)) =
      ∑ x ∈ T, ∑ q ∈ Icc 1 R,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x) := by
    simp_rw [mul_sum]
    rw [sum_comm]
  change ‖(∑ x ∈ T, _) - (∑ q ∈ Icc 1 R, _)‖ ≤ _
  rw [hswap, ← sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ T, ‖singSeries (dif x) - ∑ q ∈ Icc 1 R,
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _x ∈ T, (192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ) := sum_le_sum hpoint
    _ = (T.card : ℝ) * ((192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ)) := by simp
    _ ≤ (L : ℝ) ^ (2 * k) * ((192 * A * ((k * N : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) / (R : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 pp.134 and 135. The moving cutoff N to power one over k makes the normalized tuple truncation error vanish. -/
theorem tuple_truncation_eventually {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ‖(∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x)) -
          ∑ q ∈ Icc 1 ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊,
            ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
              ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)‖ ≤
      δ * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  obtain ⟨C, hC, hbound⟩ := tuple_singular_truncation_bound (4 * k) (by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  let e : ℝ := ((4 * k : ℕ) : ℝ)⁻¹
  let t : ℝ := (k : ℝ)⁻¹ * (3 / 4)
  have he : e - t = -((2 * (k : ℝ))⁻¹) := by
    dsimp [e, t]
    push_cast
    field_simp
    ring
  have hlim : Tendsto (fun N : ℕ => C * (k : ℝ) ^ e * (N : ℝ) ^ (-((2 * (k : ℝ))⁻¹)))
      atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop (show 0 < (2 * (k : ℝ))⁻¹ by positivity)).comp
      tendsto_natCast_atTop_atTop).const_mul (C * (k : ℝ) ^ e)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hδ))
  refine ⟨max N0 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNbase : N0 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let R : ℕ := ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊
  have hR : 0 < R := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hNpos _)
  have hden : (N : ℝ) ^ t ≤ (R : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ = ((N : ℝ) ^ ((k : ℝ)⁻¹)) ^ (3 / 4 : ℝ) := Real.rpow_mul hNpos.le _ _
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (Nat.le_ceil _) (by norm_num)
  have hratio : C * ((k * N : ℕ) : ℝ) ^ e / (R : ℝ) ^ (3 / 4 : ℝ) ≤
      C * (k : ℝ) ^ e * (N : ℝ) ^ (-((2 * (k : ℝ))⁻¹)) := by
    calc
      _ ≤ C * ((k * N : ℕ) : ℝ) ^ e / (N : ℝ) ^ t :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNpos _) hden
      _ = (C * (k : ℝ) ^ e) * ((N : ℝ) ^ e / (N : ℝ) ^ t) := by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg N)]
        ring
      _ = (C * (k : ℝ) ^ e) * (N : ℝ) ^ (e - t) := by rw [Real.rpow_sub hNpos]
      _ = _ := by rw [he]
  have hh := hbound k N R hN2 hR
  change ‖_‖ ≤ C * ((k * N : ℕ) : ℝ) ^ e * (Nat.log 2 N : ℝ) ^ (2 * k) / (R : ℝ) ^ (3 / 4 : ℝ) at hh
  change ‖_‖ ≤ δ * (Nat.log 2 N : ℝ) ^ (2 * k)
  calc
    _ ≤ _ := hh
    _ = (C * ((k * N : ℕ) : ℝ) ^ e / (R : ℝ) ^ (3 / 4 : ℝ)) * (Nat.log 2 N : ℝ) ^ (2 * k) := by ring
    _ ≤ (C * (k : ℝ) ^ e * (N : ℝ) ^ (-((2 * (k : ℝ))⁻¹))) * (Nat.log 2 N : ℝ) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (hN0 N hNbase).le (by positivity)

/-- Gallagher 1975 p.135. The complete natural residue grid has the proved modular moment bound. -/
theorem complete_nat_grid_moment_le {q : ℕ} (hq : 0 < q) (ho : Odd q) {k : ℕ} (hk : 1 ≤ k) (L : ℕ) :
    ∑ a ∈ range q, ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) ≤
      q * ((L : ℝ) ^ (2 * k) / ordTwo q + (L : ℝ) ^ (2 * k - 1)) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have heq : (∑ a ∈ range q, ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) =
      ∑ a : ZMod q, ‖Gs L ((a.val : ℝ) / q)‖ ^ (2 * k) := by
    apply sum_bij (fun (a : ℕ) (_ : a ∈ range q) => (a : ZMod q))
    · intro a ha; exact mem_univ _
    · intro a ha b hb hab
      have hh := congrArg ZMod.val hab
      simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha), ZMod.val_natCast_of_lt (mem_range.mp hb)] using hh
    · intro a ha
      exact ⟨a.val, mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha
      rw [ZMod.val_natCast_of_lt (mem_range.mp ha)]
  rw [heq]
  exact LeanLab.Linnik.Decomp1532a.Gs_grid_moment_le ho hk L

/-- Gallagher 1975 p.135. Reduced natural residues inherit a uniform small order moment gap. -/
theorem primitive_nat_grid_moment_le {q E L : ℕ} (hq : 1 < q) (ho : Odd q)
    (hE : 2 ≤ E) (heE : ordTwo q ≤ E) (hEL : E ≤ L) (k : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) ≤
      q.totient * (((1 - 1 / (16 * (E : ℝ))) * L) ^ (2 * k)) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  have he2 : 2 ≤ ordTwo q := by
    have hepos := LeanLab.Linnik.Decomp1532a.ordTwo_pos ho
    by_contra hh
    have he1 : ordTwo q = 1 := by omega
    have hd := LeanLab.Linnik.Decomp1532a.dvd_two_pow_ordTwo_sub_one ho
    rw [he1] at hd
    have hq1 : q = 1 := by simpa using hd
    omega
  have hEp : (0 : ℝ) < E := by exact_mod_cast (by omega : 0 < E)
  have hep : (0 : ℝ) < ordTwo q := by exact_mod_cast (by omega : 0 < ordTwo q)
  have hdiv : 1 / (16 * (E : ℝ)) ≤ 1 / (16 * (ordTwo q : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (by exact_mod_cast heE) (by norm_num))
  have hgap : (1 - 1 / (16 * (ordTwo q : ℝ))) * L ≤ (1 - 1 / (16 * (E : ℝ))) * L :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg L)
  have hpoint (a : ℕ) (ha : a ∈ (range q).filter (fun a => Nat.Coprime a q)) :
      ‖Gs L ((a : ℝ) / q)‖ ≤ (1 - 1 / (16 * (E : ℝ))) * L := by
    obtain ⟨haq, hac⟩ := mem_filter.mp ha
    have hg := (LeanLab.Linnik.Decomp1532a.rational_power_gap ho (ZMod.unitOfCoprime a hac) he2
      (heE.trans hEL)).le
    have hh : ‖Gs L ((a : ℝ) / q)‖ ≤ (1 - 1 / (16 * (ordTwo q : ℝ))) * L := by
      simpa only [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (mem_range.mp haq)] using hg
    exact hh.trans hgap
  have hc : #((range q).filter (fun a => Nat.Coprime a q)) = q.totient := by
    simp [Nat.totient, Nat.coprime_comm]
  calc
    _ ≤ ∑ _a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (((1 - 1 / (16 * (E : ℝ))) * L) ^ (2 * k)) := by
      apply sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ (norm_nonneg _) (hpoint a ha) _
    _ = _ := by simp [hc]

/-- Gallagher 1975 p.135. The two finite order ranges have a uniform E and R bound. -/
theorem odd_moment_order_split : ∃ C : ℝ, 0 < C ∧ ∀ k L R E : ℕ,
    1 ≤ k → 2 ≤ R → 2 ≤ E → E ≤ L →
      (∑ q ∈ Icc 3 R with Odd q,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) ≤
      C * (L : ℝ) ^ (2 * k) *
        (Real.log E / E + (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E) +
      Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log R := by
  classical
  obtain ⟨A, hA⟩ := LeanLab.Linnik.Decomp1532a.lemma4
  obtain ⟨B, hB⟩ := LeanLab.Linnik.Decomp1532a.order_weight_tail_log
  let C := |A| + |B| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith [le_abs_self A, abs_nonneg B]
  have hBC : B ≤ C := by dsimp [C]; linarith [le_abs_self B, abs_nonneg A]
  refine ⟨C, hC, fun k L R E hk hR hE hEL => ?_⟩
  let S := (Icc 3 R).filter Odd
  let Slo := S.filter (fun q => ordTwo q ≤ E)
  let Shi := S.filter (fun q => ¬ ordTwo q ≤ E)
  let w : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2
  let v : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2
  let H : ℕ → ℝ := fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)
  let G : ℝ := (1 - 1 / (16 * (E : ℝ))) * L
  have hlogE : 0 ≤ Real.log (E : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E))
  have hEp : (0 : ℝ) < E := by exact_mod_cast (by omega : 0 < E)
  have hgap0 : 0 ≤ 1 - 1 / (16 * (E : ℝ)) := by
    have hEr : (2 : ℝ) ≤ E := by exact_mod_cast hE
    have hh : 1 / (16 * (E : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hG0 : 0 ≤ G := mul_nonneg hgap0 (Nat.cast_nonneg L)
  have hw0 (q : ℕ) : 0 ≤ w q := by dsimp [w]; positivity
  have hv0 (q : ℕ) : 0 ≤ v q := by dsimp [v]; positivity
  have hlowpoint (q : ℕ) (hq : q ∈ Slo) : v q * H q ≤ w q * G ^ (2 * k) := by
    obtain ⟨hqS, hqe⟩ := mem_filter.mp hq
    obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
    have hq3 := (mem_Icc.mp hqI).1
    have hm := primitive_nat_grid_moment_le (by omega : 1 < q) hqo hE hqe hEL k
    have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    calc
      _ ≤ v q * ((q.totient : ℝ) * G ^ (2 * k)) := mul_le_mul_of_nonneg_left hm (hv0 q)
      _ ≤ v q * ((q : ℝ) * G ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ (pow_nonneg hG0 _)) (hv0 q)
      _ = _ := by dsimp [v, w]; ring
  have hlowcoeff : ∑ q ∈ Slo, w q ≤ C * Real.log E := by
    have hsub : Slo ⊆ (Icc 1 R).filter (fun q => Odd q ∧ ordTwo q ≤ E) := by
      intro q hq
      obtain ⟨hqS, hqe⟩ := mem_filter.mp hq
      obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hqI).1; omega, (mem_Icc.mp hqI).2⟩, hqo, hqe⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw0 q)).trans
      ((hA E hE R).trans (mul_le_mul_of_nonneg_right hAC hlogE))
  have hlow : (∑ q ∈ Slo, v q * H q) ≤ C * Real.log E * G ^ (2 * k) := by
    calc
      _ ≤ ∑ q ∈ Slo, w q * G ^ (2 * k) := sum_le_sum hlowpoint
      _ = (∑ q ∈ Slo, w q) * G ^ (2 * k) := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hlowcoeff (pow_nonneg hG0 _)
  have hhighpoint (q : ℕ) (hq : q ∈ Shi) : v q * H q ≤
      (L : ℝ) ^ (2 * k) * (w q / ordTwo q) + (L : ℝ) ^ (2 * k - 1) * w q := by
    have hqS := (mem_filter.mp hq).1
    obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
    have hq3 := (mem_Icc.mp hqI).1
    have hfull : H q ≤ ∑ a ∈ range q, ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    have hm := complete_nat_grid_moment_le (by omega : 0 < q) hqo hk L
    calc
      _ ≤ v q * ((q : ℝ) * ((L : ℝ) ^ (2 * k) / ordTwo q + (L : ℝ) ^ (2 * k - 1))) :=
        mul_le_mul_of_nonneg_left (hfull.trans hm) (hv0 q)
      _ = _ := by dsimp [v, w]; ring
  have htail : (∑ q ∈ Shi, w q / ordTwo q) ≤ C * Real.log E / E := by
    have he : Shi = (Icc 3 R).filter (fun q => Odd q ∧ E < ordTwo q) := by
      ext q
      simp only [Shi, S, mem_filter, not_le]
      tauto
    rw [he]
    exact (hB E hE (Icc 3 R)).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hlogE) hEp.le)
  have hhighcoeff : ∑ q ∈ Shi, w q ≤ Real.exp 24 * Real.log R := by
    have hsub : Shi ⊆ (Icc 1 R).filter Odd := by
      intro q hq
      obtain ⟨hqS, _⟩ := mem_filter.mp hq
      obtain ⟨hqI, hqo⟩ := mem_filter.mp hqS
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hqI).1; omega, (mem_Icc.mp hqI).2⟩, hqo⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw0 q)).trans
      (LeanLab.Linnik.Decomp1532a.totient_square_sum_le_log hR)
  have hhigh : (∑ q ∈ Shi, v q * H q) ≤
      (L : ℝ) ^ (2 * k) * (C * Real.log E / E) +
        (L : ℝ) ^ (2 * k - 1) * (Real.exp 24 * Real.log R) := by
    calc
      _ ≤ ∑ q ∈ Shi, ((L : ℝ) ^ (2 * k) * (w q / ordTwo q) + (L : ℝ) ^ (2 * k - 1) * w q) := sum_le_sum hhighpoint
      _ = (L : ℝ) ^ (2 * k) * (∑ q ∈ Shi, w q / ordTwo q) + (L : ℝ) ^ (2 * k - 1) * ∑ q ∈ Shi, w q := by
        rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left htail (by positivity))
        (mul_le_mul_of_nonneg_left hhighcoeff (by positivity))
  have heq : (∑ q ∈ S, v q * H q) = (∑ q ∈ Slo, v q * H q) + ∑ q ∈ Shi, v q * H q :=
    (sum_filter_add_sum_filter_not S (fun q => ordTwo q ≤ E) (fun q => v q * H q)).symm
  change (∑ q ∈ S, v q * H q) ≤ _
  rw [heq]
  calc
    _ ≤ C * Real.log E * G ^ (2 * k) +
        ((L : ℝ) ^ (2 * k) * (C * Real.log E / E) + (L : ℝ) ^ (2 * k - 1) * (Real.exp 24 * Real.log R)) :=
      add_le_add hlow hhigh
    _ = _ := by dsimp [G]; rw [mul_pow]; ring

/-- Gallagher 1975 p.135. Choosing the order cutoff proportional to k over log k gives the stated error scale. -/
theorem order_parameter_choice : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
    ∃ E : ℕ, 2 ≤ E ∧ E ≤ k ∧
      Real.log E / E + (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E ≤
        C * (Real.log k ^ 2 / k) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := 65536 / Real.log (2 : ℝ) ^ 2 + 65
  have hC : 0 < C := by dsimp [C]; positivity
  have hC65 : 65 ≤ C := by
    dsimp [C]
    have hd : 0 ≤ 65536 / Real.log (2 : ℝ) ^ 2 := by positivity
    linarith
  refine ⟨C, hC, fun k hk => ?_⟩
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlk : Real.log (2 : ℝ) ≤ Real.log k := Real.log_le_log (by norm_num) hkR
  have hlk0 : 0 < Real.log (k : ℝ) := hl2.trans_le hlk
  by_cases hlarge : 16384 ≤ k
  · have hkbig : (16384 : ℝ) ≤ k := by exact_mod_cast hlarge
    have hlk1 : 1 ≤ Real.log (k : ℝ) := by
      apply le_of_lt
      rw [Real.lt_log_iff_exp_lt hk0]
      linarith [Real.exp_one_lt_d9]
    have hroot : (128 : ℝ) ≤ Real.sqrt k := Real.le_sqrt_of_sq_le (by nlinarith)
    have hlogroot : Real.log (k : ℝ) ≤ 2 * Real.sqrt k := by
      have hh := Real.log_le_rpow_div (Nat.cast_nonneg k) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at hh
      linarith
    have h64 : 64 * Real.log (k : ℝ) ≤ k := by
      have hp := mul_nonneg (sub_nonneg.mpr hroot) (Real.sqrt_nonneg (k : ℝ))
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg k)]
    let x : ℝ := (k : ℝ) / (32 * Real.log k)
    let E : ℕ := ⌊x⌋₊
    have hx2 : 2 ≤ x := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hE2 : 2 ≤ E := Nat.le_floor hx2
    have hEreal : (2 : ℝ) ≤ E := by exact_mod_cast hE2
    have hEp : (0 : ℝ) < E := by linarith
    have hElo : (E : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hEhalf : x / 2 ≤ E := by
      have hh := Nat.lt_floor_add_one x
      change x < (E : ℝ) + 1 at hh
      linarith
    have hxk : x ≤ k := div_le_self hk0.le (by linarith)
    have hEk : E ≤ k := by exact_mod_cast hElo.trans hxk
    have hElog : Real.log (E : ℝ) ≤ Real.log k := Real.log_le_log hEp (by exact_mod_cast hEk)
    have hElog0 : 0 ≤ Real.log (E : ℝ) := Real.log_nonneg (by linarith)
    have hEden : (k : ℝ) / (64 * Real.log k) ≤ E := by
      calc _ = x / 2 := by dsimp [x]; ring
           _ ≤ _ := hEhalf
    have hmain : Real.log (E : ℝ) / E ≤ 64 * Real.log k ^ 2 / k := by
      calc
        _ ≤ Real.log (k : ℝ) / E := div_le_div_of_nonneg_right hElog hEp.le
        _ ≤ Real.log (k : ℝ) / ((k : ℝ) / (64 * Real.log k)) :=
          div_le_div_of_nonneg_left hlk0.le (by positivity) hEden
        _ = _ := by field_simp
    have hgap0 : 0 ≤ 1 - 1 / (16 * (E : ℝ)) := by
      have hh : 1 / (16 * (E : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      linarith
    have hbase : 1 - 1 / (16 * (E : ℝ)) ≤ Real.exp (-1 / (16 * (E : ℝ))) := by
      simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-1 / (16 * (E : ℝ)))
    have hprod : (E : ℝ) * (32 * Real.log k) ≤ k := (le_div_iff₀ (by positivity)).mp hElo
    have hexponent : -(k : ℝ) / (8 * E) ≤ -4 * Real.log k := by
      have hh : 4 * Real.log k ≤ (k : ℝ) / (8 * E) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
      simpa only [neg_div, neg_mul] using neg_le_neg hh
    have hpow : (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) ≤ 1 / (k : ℝ) := by
      calc
        _ ≤ Real.exp (-1 / (16 * (E : ℝ))) ^ (2 * k) := pow_le_pow_left₀ hgap0 hbase _
        _ = Real.exp (-(k : ℝ) / (8 * E)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        _ ≤ Real.exp (-4 * Real.log k) := Real.exp_le_exp.mpr hexponent
        _ = (k : ℝ) ^ (-4 : ℝ) := by rw [Real.rpow_def_of_pos hk0]; congr 1; ring
        _ ≤ (k : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ k by linarith) (by norm_num)
        _ = _ := by simp only [Real.rpow_neg_one, one_div]
    have hsmall : (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E ≤ Real.log k ^ 2 / k := by
      calc
        _ ≤ (1 / (k : ℝ)) * Real.log k := mul_le_mul hpow hElog hElog0 (by positivity)
        _ = Real.log k / k := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hk0.le
    refine ⟨E, hE2, hEk, ?_⟩
    calc
      _ ≤ 65 * (Real.log k ^ 2 / k) := by
        calc
          _ ≤ 64 * Real.log k ^ 2 / k + Real.log k ^ 2 / k := add_le_add hmain hsmall
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC65 (by positivity)
  · have hksmall : (k : ℝ) ≤ 16384 := by exact_mod_cast (by omega : k ≤ 16384)
    have hsq : Real.log (2 : ℝ) ^ 2 ≤ Real.log k ^ 2 := pow_le_pow_left₀ hl2.le hlk 2
    have hCprod : 65536 ≤ C * Real.log k ^ 2 := by
      calc
        _ = (65536 / Real.log (2 : ℝ) ^ 2) * Real.log (2 : ℝ) ^ 2 := by field_simp
        _ ≤ (65536 / Real.log (2 : ℝ) ^ 2) * Real.log k ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _)
    have htarget : 2 ≤ C * (Real.log k ^ 2 / k) := by
      rw [← mul_div_assoc, le_div_iff₀ hk0]
      nlinarith
    have hpow : (1 - 1 / (16 * (2 : ℝ))) ^ (2 * k) ≤ 1 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 - 1 / (16 * 2))
        (by norm_num : 1 - 1 / (16 * (2 : ℝ)) ≤ 1) (2 * k)
    have hl2le : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh : Real.log (2 : ℝ) / 2 + (1 - 1 / (16 * (2 : ℝ))) ^ (2 * k) * Real.log 2 ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_right hpow hl2.le
      nlinarith
    exact ⟨2, le_rfl, hk, hh.trans htarget⟩

/-- Gallagher 1975 p.134. At even frequencies the singular coefficients at odd q and twice q agree. -/
theorem singular_coefficient_double_even {r : ℕ} (hr : Odd r) {n : ℤ} (hn : Even n) :
    ((ArithmeticFunction.moebius (2 * r) : ℤ) : ℂ) ^ 2 / ((2 * r).totient : ℂ) ^ 2 * ramanujanSum (2 * r) n =
      ((ArithmeticFunction.moebius r : ℤ) : ℂ) ^ 2 / (r.totient : ℂ) ^ 2 * ramanujanSum r n := by
  by_cases hsf : Squarefree r
  · have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
    have hsf2 : Squarefree (2 * r) := (Nat.squarefree_mul hcop).mpr ⟨Nat.squarefree_two, hsf⟩
    obtain ⟨t, ht⟩ : ∃ t : ℕ, n.natAbs = 2 * t := by
      obtain ⟨t, ht⟩ := Int.natAbs_even.mpr hn
      exact ⟨t, by omega⟩
    have hcancel : Nat.gcd r (2 * t) = Nat.gcd r t := by
      simpa [Nat.gcd_comm] using hcop.gcd_mul_left_cancel t
    have hg : Nat.gcd (2 * r) n.natAbs = 2 * Nat.gcd r n.natAbs := by
      rw [ht, Nat.gcd_mul_left, hcancel]
    have hgodd : Odd (Nat.gcd r n.natAbs) := hr.of_dvd_nat (Nat.gcd_dvd_left r n.natAbs)
    have hquot : (2 * r) / (2 * Nat.gcd r n.natAbs) = r / Nat.gcd r n.natAbs :=
      Nat.mul_div_mul_left r (Nat.gcd r n.natAbs) (by decide)
    have hm1 : ((ArithmeticFunction.moebius r : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    have hm2 : ((ArithmeticFunction.moebius (2 * r) : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf2
    rw [ramanujanSum_squarefree hsf2 n, ramanujanSum_squarefree hsf n, hg, hquot,
      Nat.totient_mul hcop, Nat.totient_two_mul_of_odd hgodd, hm1, hm2]
    norm_num
  · have hsf2 : ¬ Squarefree (2 * r) := fun h => hsf h.of_mul_right
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf2]

/-- Gallagher 1975 p.134. Finite parity pairing costs at most a factor two and a doubled cutoff. -/
theorem finite_parity_pair_bound (A : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q)
    (hfour : ∀ q, A (4 * q) = 0) (hdouble : ∀ q, Odd q → A (2 * q) = A q)
    {R : ℕ} (hR : 1 ≤ R) :
    ∑ q ∈ Icc 1 R, A q ≤ 2 * ∑ q ∈ Icc 1 (2 * R) with Odd q, A q := by
  classical
  let O := (Icc 1 R).filter Odd
  let V := (Icc 1 R).filter (fun q => ¬ Odd q)
  let G := V.filter (fun q => Odd (q / 2))
  let T := (Icc 1 (2 * R)).filter Odd
  have heven (q : ℕ) (hq : q ∈ V) : 2 * (q / 2) = q := by
    have hn := (mem_filter.mp hq).2
    have he : Even q := (Nat.even_or_odd q).resolve_right hn
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp he)
  have hpoint (q : ℕ) (hq : q ∈ V) : A q = if Odd (q / 2) then A (q / 2) else 0 := by
    have hq2 := heven q hq
    by_cases ho : Odd (q / 2)
    · rw [ite_eq_left ho]
      calc _ = A (2 * (q / 2)) := congrArg A hq2.symm
           _ = _ := hdouble _ ho
    · rw [ite_eq_right ho]
      obtain ⟨u, hu⟩ := (Nat.even_or_odd (q / 2)).resolve_right ho
      have hh : q = 4 * u := by omega
      rw [hh, hfour]
  have hinj : Set.InjOn (fun q : ℕ => q / 2) (G : Set ℕ) := by
    intro a ha b hb hab
    have h1 := heven a (mem_filter.mp ha).1
    have h2 := heven b (mem_filter.mp hb).1
    change a / 2 = b / 2 at hab
    omega
  have hsub : G.image (fun q => q / 2) ⊆ T := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
    obtain ⟨hqV, hqo⟩ := mem_filter.mp hq
    have hqI := (mem_filter.mp hqV).1
    have hq2 := heven q hqV
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp hqI).1; omega, ?_⟩, hqo⟩
    have hqR := (mem_Icc.mp hqI).2
    have hhalf := Nat.div_le_self q 2
    omega
  have heq : (∑ q ∈ V, A q) = ∑ r ∈ G.image (fun q => q / 2), A r := by
    rw [sum_congr rfl hpoint, ← sum_filter, sum_image hinj]
  have hV : (∑ q ∈ V, A q) ≤ ∑ q ∈ T, A q :=
    heq.trans_le (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hA q))
  have hO : (∑ q ∈ O, A q) ≤ ∑ q ∈ T, A q := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hA q)
    intro q hq
    obtain ⟨hqI, hqo⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hqI).1, by have := (mem_Icc.mp hqI).2; omega⟩, hqo⟩
  have hs := sum_filter_add_sum_filter_not (Icc 1 R) Odd A
  change (∑ q ∈ O, A q) + (∑ q ∈ V, A q) = _ at hs
  rw [← hs]
  change _ ≤ 2 * ∑ q ∈ T, A q
  linarith

/-- Gallagher 1975 p.135. The moving cutoff has the logarithmic size needed in the order split. -/
theorem l6_cutoff_bounds {k N : ℕ} (hk : 2 ≤ k) (hN : 2 ^ k ≤ N) :
    k ≤ Nat.log 2 N ∧ 2 ≤ ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊ ∧
      Real.log ((2 * ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊ : ℕ) : ℝ) ≤
        4 * Real.log 2 * (Nat.log 2 N : ℝ) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hN2 : 2 ≤ N := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
         _ ≤ N := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let L := Nat.log 2 N
  let x : ℝ := (N : ℝ) ^ ((k : ℝ)⁻¹)
  let R : ℕ := ⌈x⌉₊
  have hL : k ≤ L := Nat.le_log_of_pow_le (by norm_num) hN
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hx2 : 2 ≤ x := by
    calc
      _ = ((2 : ℝ) ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (by norm_num) (by omega : k ≠ 0)).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by positivity)
  have hR2 : 2 ≤ R := by exact_mod_cast hx2.trans (Nat.le_ceil x)
  have hRup : (R : ℝ) ≤ 2 * x := by
    have hh : (R : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hNlog : Real.log (N : ℝ) ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have hb : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le
    have hh := Real.log_le_log hN0 hb
    rw [Real.log_pow] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have h4log : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hxlog : Real.log x = (k : ℝ)⁻¹ * Real.log N := Real.log_rpow hN0 _
  have hlogR : Real.log ((2 * R : ℕ) : ℝ) ≤ 2 * Real.log 2 + (k : ℝ)⁻¹ * Real.log N := by
    have hp : (0 : ℝ) < ((2 * R : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * R)
    have hb : ((2 * R : ℕ) : ℝ) ≤ 4 * x := by push_cast; linarith
    have hh := Real.log_le_log hp hb
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx0.ne', h4log, hxlog] at hh
    exact hh
  refine ⟨hL, hR2, ?_⟩
  change Real.log ((2 * R : ℕ) : ℝ) ≤ 4 * Real.log 2 * (L : ℝ) / k
  rw [le_div_iff₀ hk0]
  have hh := mul_le_mul_of_nonneg_right hlogR hk0.le
  have he : (2 * Real.log 2 + (k : ℝ)⁻¹ * Real.log N) * k = 2 * Real.log 2 * k + Real.log N := by
    field_simp <;> ring
  rw [he] at hh
  have hkL : (k : ℝ) ≤ L := by exact_mod_cast hL
  have hm := mul_le_mul_of_nonneg_left hkL (show 0 ≤ 2 * Real.log 2 by positivity)
  have hlN : Real.log (N : ℝ) ≤ 2 * L * Real.log 2 := by nlinarith
  nlinarith

/-- Gallagher 1975 p.135. The finite logarithm error is absorbed at the final k scale. -/
theorem l6_log_error_le {k L Q : ℕ} (hk : 2 ≤ k)
    (hlog : Real.log (Q : ℝ) ≤ 4 * Real.log 2 * (L : ℝ) / k) :
    Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log Q ≤
      (4 * Real.exp 24 / Real.log 2) * (Real.log k ^ 2 / k) * (L : ℝ) ^ (2 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogk : Real.log (2 : ℝ) ≤ Real.log k := Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hsq : Real.log (2 : ℝ) ^ 2 ≤ Real.log k ^ 2 := pow_le_pow_left₀ hl2.le hlogk 2
  have hcoef : 4 * Real.exp 24 * Real.log 2 / k ≤
      (4 * Real.exp 24 / Real.log 2) * (Real.log k ^ 2 / k) := by
    calc
      _ = (4 * Real.exp 24 / Real.log 2) * (Real.log (2 : ℝ) ^ 2 / k) := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq hk0.le) (by positivity)
  have hp : (L : ℝ) ^ (2 * k - 1) * L = (L : ℝ) ^ (2 * k) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ ≤ Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * (4 * Real.log 2 * L / k) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (4 * Real.exp 24 * Real.log 2 / k) * ((L : ℝ) ^ (2 * k - 1) * L) := by ring
    _ = (4 * Real.exp 24 * Real.log 2 / k) * (L : ℝ) ^ (2 * k) := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- Gallagher 1975 pp.134 and 135. The restored weighted tuple sum is a nonnegative real rational moment. -/
theorem ramanujan_moment_coefficient (q k L : ℕ) :
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        (∑ x : pairs k L, ramanujanSum q (dif x)) =
      ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)) : ℝ) : ℂ) := by
  rw [ramanujan_tuple_sum_eq, ← Complex.ofReal_sum]
  push_cast <;> rfl

/-- Gallagher 1975 p.134. The finite zero frequency contribution is its tuple count times the reciprocal totient coefficient sum. -/
theorem finite_singular_diagonal_eq (k L : ℕ) (S : Finset ℕ) :
    (∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) =
    (((#{x : pairs k L | dif x = 0} : ℝ) *
      (∑ q ∈ S, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
  classical
  let D := #{x : pairs k L | dif x = 0}
  have hinner (q : ℕ) : (∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) = (D : ℂ) * q.totient := by
    calc
      _ = ∑ _x : pairs k L with dif _x = 0, (q.totient : ℂ) := by
        apply sum_congr rfl
        intro x hx
        rw [(mem_filter.mp hx).2, ramanujanSum_zero]
      _ = _ := by simp [D, nsmul_eq_mul]
  have hterm (q : ℕ) :
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x) =
      (((D : ℝ) * (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)) : ℝ) : ℂ) := by
    by_cases hq : q = 0
    · simp [hq]
    have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
    rw [hinner]
    push_cast
    field_simp
  rw [sum_congr rfl (fun q _ => hterm q), ← Complex.ofReal_sum, ← mul_sum]

/-- Gallagher 1975 p.134. The rational moment has the parity pairing and its first main term. -/
theorem rational_moment_parity (k L : ℕ) :
    let A : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)
    (∀ q, 0 ≤ A q) ∧ (∀ q, A (4 * q) = 0) ∧
      (∀ q, Odd q → A (2 * q) = A q) ∧ A 1 = (L : ℝ) ^ (2 * k) := by
  classical
  dsimp only
  refine ⟨fun q => by positivity, ?_, ?_, ?_⟩
  · intro q
    have hs : ¬ Squarefree (4 * q) := by
      intro h
      exact (by norm_num : ¬ IsUnit (2 : ℕ)) (h 2 (by omega))
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · intro q hq
    apply Complex.ofReal_injective
    rw [← ramanujan_moment_coefficient, ← ramanujan_moment_coefficient, mul_sum, mul_sum]
    apply sum_congr rfl
    intro x hx
    apply singular_coefficient_double_even hq
    have h1 : Even (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℤ) := by
      exact_mod_cast (Nat.even_iff.mpr (LeanLab.Linnik.U1434Lemma21.sv_even x.1))
    have h2 : Even (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℤ) := by
      exact_mod_cast (Nat.even_iff.mpr (LeanLab.Linnik.U1434Lemma21.sv_even x.2))
    exact h1.sub h2
  · apply Complex.ofReal_injective
    rw [← ramanujan_moment_coefficient, ramanujan_tuple_sum_one]
    push_cast
    simp

/-- Gallagher 1975 p.134. The diagonal reciprocal totient coefficient has the same parity pairing. -/
theorem reciprocal_totient_parity :
    let B : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)
    (∀ q, 0 ≤ B q) ∧ (∀ q, B (4 * q) = 0) ∧ (∀ q, Odd q → B (2 * q) = B q) := by
  refine ⟨fun q => by positivity, ?_, ?_⟩
  · intro q
    have hs : ¬ Squarefree (4 * q) := by
      intro h
      exact (by norm_num : ¬ IsUnit (2 : ℕ)) (h 2 (by omega))
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · intro q hq
    have hc : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq
    dsimp only
    rw [Nat.totient_mul hc, Nat.totient_two, one_mul]
    by_cases hs : Squarefree q
    · have hs2 : Squarefree (2 * q) := (Nat.squarefree_mul hc).mpr ⟨Nat.squarefree_two, hs⟩
      rw [show ((ArithmeticFunction.moebius (2 * q) : ℤ) : ℝ) ^ 2 = 1 by exact_mod_cast (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs2),
        show ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 = 1 by exact_mod_cast (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs)]
    · have hs2 : ¬ Squarefree (2 * q) := fun h => hs h.of_mul_right
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs2]

/-- Gallagher 1975 pp.134 and 135. The growing finite truncation has the required main term estimate. -/
theorem finite_singular_main_bound : ∃ C : ℝ, 0 < C ∧ ∀ k N : ℕ, 2 ≤ k → 2 ^ k ≤ N →
    ‖(∑ q ∈ Icc 1 ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊,
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)) -
      2 * (Nat.log 2 N : ℂ) ^ (2 * k)‖ ≤
      C * (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C₁, hC₁, hsplit⟩ := odd_moment_order_split
  obtain ⟨C₂, hC₂, hparam⟩ := order_parameter_choice
  let D : ℝ := 4 * Real.exp 24 / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨2 * C₁ * C₂ + 6 * D, by positivity, fun k N hk hN => ?_⟩
  let L := Nat.log 2 N
  let R := ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊
  let Q := 2 * R
  let a : ℝ := Real.log k ^ 2 / k
  let P : ℝ := (L : ℝ) ^ (2 * k)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨hkL, hR, hlog⟩ := l6_cutoff_bounds hk hN
  have hQ : 2 ≤ Q := by dsimp [Q]; omega
  obtain ⟨E, hE, hEk, hchoice⟩ := hparam k hk
  have hEL : E ≤ L := hEk.trans hkL
  let A : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖Gs L ((a : ℝ) / q)‖ ^ (2 * k)
  let B : ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ)
  obtain ⟨hA0, hA4, hA2, hA1⟩ := rational_moment_parity k L
  obtain ⟨hB0, hB4, hB2⟩ := reciprocal_totient_parity
  have hoddset : (Icc 1 Q).filter Odd = insert 1 ((Icc 3 Q).filter Odd) := by
    ext q
    simp only [mem_filter, mem_Icc, mem_insert]
    constructor
    · rintro ⟨⟨h1, hQq⟩, ho⟩
      by_cases he : q = 1
      · exact Or.inl he
      · right
        have hne : q ≠ 2 := by intro h; subst q; norm_num at ho
        exact ⟨⟨by omega, hQq⟩, ho⟩
    · rintro (rfl | ⟨⟨h3, hQq⟩, ho⟩)
      · exact ⟨⟨by omega, by omega⟩, by decide⟩
      · exact ⟨⟨by omega, hQq⟩, ho⟩
  have hodd : (∑ q ∈ (Icc 1 Q).filter Odd, A q) = P + ∑ q ∈ (Icc 3 Q).filter Odd, A q := by
    rw [hoddset, sum_insert (by simp)]
    rw [show A 1 = P from hA1]
  have herror := l6_log_error_le (L := L) (Q := Q) hk hlog
  change Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log Q ≤ D * a * P at herror
  have hoddle : (∑ q ∈ (Icc 3 Q).filter Odd, A q) ≤ (C₁ * C₂ + D) * a * P := by
    have hh := hsplit k L Q E (by omega) hQ hE hEL
    change (∑ q ∈ (Icc 3 Q).filter Odd, A q) ≤ _ at hh
    have hm := mul_le_mul_of_nonneg_left hchoice (show 0 ≤ C₁ * P by positivity)
    change C₁ * P * (Real.log E / E + (1 - 1 / (16 * (E : ℝ))) ^ (2 * k) * Real.log E) ≤ C₁ * P * (C₂ * a) at hm
    change (∑ q ∈ (Icc 3 Q).filter Odd, A q) ≤ C₁ * P * _ + _ at hh
    nlinarith
  have hSupper : (∑ q ∈ Icc 1 R, A q) - 2 * P ≤ 2 * (C₁ * C₂ + D) * a * P := by
    have hh := finite_parity_pair_bound A hA0 hA4 hA2 (by omega : 1 ≤ R)
    change (∑ q ∈ Icc 1 R, A q) ≤ 2 * ∑ q ∈ (Icc 1 Q).filter Odd, A q at hh
    rw [hodd] at hh
    linarith
  have hSlower : 2 * P ≤ ∑ q ∈ Icc 1 R, A q := by
    have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 R := by intro q hq; simp only [mem_insert, mem_singleton] at hq; rcases hq with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hh := sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hA0 q)
    have hA2one : A 2 = P := (hA2 1 (by decide)).trans hA1
    rw [sum_pair (by decide)] at hh
    change A 1 + A 2 ≤ _ at hh
    rw [show A 1 = P from hA1, hA2one] at hh
    linarith
  have hrest : ‖(∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k)‖ ≤ 2 * (C₁ * C₂ + D) * a * P := by
    have heq : (∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k) =
      (((∑ q ∈ Icc 1 R, A q) - 2 * P : ℝ) : ℂ) := by
      rw [sum_congr rfl (fun q _ => ramanujan_moment_coefficient q k L)]
      simp only [A, P, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_sum]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hSlower)]
    exact hSupper
  have hBsum : (∑ q ∈ Icc 1 R, B q) ≤ 2 * Real.exp 24 * Real.log Q := by
    have hh := finite_parity_pair_bound B hB0 hB4 hB2 (by omega : 1 ≤ R)
    have hb := reciprocal_totient_sum_le_log hQ
    change (∑ q ∈ (Icc 1 Q).filter Odd, B q) ≤ _ at hb
    change (∑ q ∈ Icc 1 R, B q) ≤ 2 * ∑ q ∈ (Icc 1 Q).filter Odd, B q at hh
    linarith
  have hdiag : ‖∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)‖ ≤ 4 * D * a * P := by
    rw [finite_singular_diagonal_eq, Complex.norm_real, Real.norm_eq_abs]
    have hb0 : 0 ≤ ∑ q ∈ Icc 1 R, B q := sum_nonneg (fun q _ => hB0 q)
    change |(#{x : pairs k L | dif x = 0} : ℝ) * (∑ q ∈ Icc 1 R, B q)| ≤ _
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hb0)]
    have hd : (#{x : pairs k L | dif x = 0} : ℝ) ≤ 2 * (L : ℝ) ^ (2 * k - 1) := by
      have hh : (#{x : pairs k L | dif x = 0} : ℝ) ≤ 2 * (L : ℝ) ^ (2 * k - 2) := by exact_mod_cast LeanLab.Linnik.Decomp1532a.rkk_zero_le hk L
      have hp : (L : ℝ) ^ (2 * k - 2) ≤ (L : ℝ) ^ (2 * k - 1) := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) (by omega)
      linarith
    calc
      _ ≤ (2 * (L : ℝ) ^ (2 * k - 1)) * (2 * Real.exp 24 * Real.log Q) := mul_le_mul hd hBsum hb0 (by positivity)
      _ = 4 * (Real.exp 24 * (L : ℝ) ^ (2 * k - 1) * Real.log Q) := by ring
      _ ≤ 4 * (D * a * P) := mul_le_mul_of_nonneg_left herror (by norm_num)
      _ = _ := by ring
  have hexpand : (∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x ≠ 0, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k) =
    ((∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L, ramanujanSum q (dif x)) - 2 * (L : ℂ) ^ (2 * k)) -
    (∑ q ∈ Icc 1 R, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x)) := by
    have hpart (q : ℕ) : (∑ x : pairs k L, ramanujanSum q (dif x)) =
      (∑ x : pairs k L with dif x ≠ 0, ramanujanSum q (dif x)) +
      ∑ x : pairs k L with dif x = 0, ramanujanSum q (dif x) := by
      simpa only [not_ne_iff] using (sum_filter_add_sum_filter_not univ (fun x : pairs k L => dif x ≠ 0) (fun x => ramanujanSum q (dif x))).symm
    simp_rw [hpart, mul_add]
    rw [sum_add_distrib]
    ring
  change ‖(∑ q ∈ Icc 1 R, _) - 2 * (L : ℂ) ^ (2 * k)‖ ≤ (2 * C₁ * C₂ + 6 * D) * a * P
  rw [hexpand]
  exact (norm_sub_le _ _).trans ((add_le_add hrest hdiag).trans_eq (by ring))

/-- LEAF. Unit U-1532. Lemma 10, display (8) p. 136: for `1 ≤ k ≤ N` and `r` of the form (7)
with `1 < r ≤ N`, `Σ_{n ≠ 0} r_{k,k}(n) |n|/φ(|n|) · r φ((r, n))/φ(r)² ≤ C L^{2k}/(log r)^{1/3}`
with an absolute `C`. -/
theorem lemma10 : ∃ C : ℝ, ∀ k N r : ℕ, 1 ≤ k → k ≤ N → 1 < r → r ≤ N →
    (∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀)) →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) *
        ((r : ℝ) * (Nat.gcd r (dif x).natAbs).totient / (r.totient : ℝ) ^ 2) ≤
      C * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log r ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨A, hA, hrestrict⟩ := restricted_tuple_totient_bound
  obtain ⟨B, hB, hdecay⟩ := exceptional_divisor_log_decay
  refine ⟨8 * A * B, fun k N r hk hkN hr hrN hshape => ?_⟩
  obtain ⟨s, hsodd, hssf, hrs⟩ := hshape
  have hs : 0 < s := hsodd.pos
  have hsr : s ≤ r := by rcases hrs with h | h | h <;> omega
  have hr3 : 3 ≤ r := by
    have hs2 : s ≠ 2 := by rintro rfl; norm_num at hsodd
    rcases hrs with h | h | h <;> omega
  have hN : 2 ≤ N := by omega
  let L := Nat.log 2 N
  let T := (univ : Finset (pairs k L)).filter (fun x => dif x ≠ 0)
  let w : pairs k L → ℝ := fun x => ((dif x).natAbs : ℝ) / (dif x).natAbs.totient
  have hw (x : pairs k L) : 0 ≤ w x := by dsimp [w]; positivity
  have hred := weighted_gcd_divisor_reduction T (fun x => (dif x).natAbs) w
    (fun x _ => hw x) hs hrs
  have hsum : (∑ f ∈ s.divisors, (f.totient : ℝ) *
        ∑ x ∈ T with f ∣ (dif x).natAbs, w x) ≤
      A * (L : ℝ) ^ (2 * k) *
        (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f)) := by
    calc
      _ ≤ ∑ f ∈ s.divisors, (f.totient : ℝ) *
          (A * (L : ℝ) ^ (2 * k) / Real.sqrt (1 + Real.log f)) := by
        apply sum_le_sum
        intro f hfd
        have hdiv := Nat.dvd_of_mem_divisors hfd
        have hfo := hsodd.of_dvd_nat hdiv
        have hfN : f ≤ N := (Nat.le_of_dvd hs hdiv).trans (hsr.trans hrN)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hh := hrestrict k N hk hkN hN f hfo hfN
        simpa only [T, w, filter_filter, Int.natCast_dvd] using hh
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro f hf
        ring
  change (∑ x ∈ T, w x * _) ≤ _
  calc
    _ ≤ (8 * r / (r.totient : ℝ) ^ 2) *
        ∑ f ∈ s.divisors, (f.totient : ℝ) * ∑ x ∈ T with f ∣ (dif x).natAbs, w x := hred
    _ ≤ (8 * r / (r.totient : ℝ) ^ 2) *
        (A * (L : ℝ) ^ (2 * k) *
          (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (8 * A * (L : ℝ) ^ (2 * k)) *
        ((r : ℝ) / (r.totient : ℝ) ^ 2 *
          (∑ f ∈ s.divisors, (f.totient : ℝ) / Real.sqrt (1 + Real.log f))) := by ring
    _ ≤ (8 * A * (L : ℝ) ^ (2 * k)) * (B / Real.log r ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hdecay r s hr3 hs hrs) (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 p.127. The exceptional character has at most one zero in the height box. -/
theorem page_zero_unique : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    ∀ ρ₁ ρ₂ : ℂ, x.2.LFunction ρ₁ = 0 → x.2.LFunction ρ₂ = 0 →
      1 - b / Real.log T ≤ ρ₁.re → |ρ₁.im| ≤ T →
      1 - b / Real.log T ≤ ρ₂.re → |ρ₂.im| ≤ T → ρ₁ = ρ₂ := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨K, hK, hKlog⟩ := log_Bt_le_log_height
  obtain ⟨c, hc, hpage⟩ := page_two_zeros
  let b := min (min br bn) (c / K)
  have hbbr : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbbn : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hbc : b ≤ c / K := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) (by positivity), ?_⟩
  intro T hT x hx ρ₁ ρ₂ hz₁ hz₂ hb₁ ht₁ hb₂ ht₂
  have hχ := hn T hT x (excSet_mono hbbn hT hx)
  have hxbr := excSet_mono hbbr hT hx
  have hmono (ρ : ℂ) (hh : 1 - b / Real.log T ≤ ρ.re) :
      1 - br / Real.log T ≤ ρ.re := by
    have hd := div_le_div_of_nonneg_right hbbr (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him₁ := (hr T hT x hxbr).2 ρ₁ hz₁ (hmono ρ₁ hb₁) ht₁
  have him₂ := (hr T hT x hxbr).2 ρ₂ hz₂ (hmono ρ₂ hb₂) ht₂
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlB : 0 < Real.log (Bt (x.1 + 1) 0) := by
    linarith [one_le_log_Bt (N := x.1 + 1) 0]
  have hcmp : b / Real.log T ≤ c / Real.log (Bt (x.1 + 1) 0) := by
    calc
      b / Real.log T ≤ (c / K) / Real.log T := div_le_div_of_nonneg_right hbc hlT.le
      _ = c / (K * Real.log T) := by rw [div_div]
      _ ≤ c / Real.log (Bt (x.1 + 1) 0) :=
        div_le_div_of_nonneg_left hc.le hlB
          (hKlog hT (by simpa using hx.1) (by simp; linarith : |(0 : ℝ)| ≤ T))
  exact hpage (x.1 + 1) x.2 hχ ρ₁ ρ₂ hz₁ hz₂ (by linarith)
    (by rw [him₁, abs_zero]; positivity) (by linarith)
    (by rw [him₂, abs_zero]; positivity)

/-- Gallagher 1975 p.127. Every exceptional zero in a sufficiently narrow height box is simple. -/
theorem page_zero_simple : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    ∀ ρ : ℂ, x.2.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      analyticOrderNatAt x.2.LFunction ρ = 1 := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨K, hK, hKlog⟩ := log_Bt_le_log_height
  obtain ⟨c, hc, hc31, hcount⟩ := page_count
  let b := min (min br bn) (c / K)
  have hbbr : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbbn : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hbc : b ≤ c / K := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) (by positivity), ?_⟩
  intro T hT x hx ρ hz hb ht
  have hχ := hn T hT x (excSet_mono hbbn hT hx)
  have hxbr := excSet_mono hbbr hT hx
  have hβbr : 1 - br / Real.log T ≤ ρ.re := by
    have hd := div_le_div_of_nonneg_right hbbr (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him := (hr T hT x hxbr).2 ρ hz hβbr ht
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlB : 0 < Real.log (Bt (x.1 + 1) 0) := by
    linarith [one_le_log_Bt (N := x.1 + 1) 0]
  have hcmp : b / Real.log T ≤ c / Real.log (Bt (x.1 + 1) 0) := by
    calc
      b / Real.log T ≤ (c / K) / Real.log T := div_le_div_of_nonneg_right hbc hlT.le
      _ = c / (K * Real.log T) := by rw [div_div]
      _ ≤ c / Real.log (Bt (x.1 + 1) 0) :=
        div_le_div_of_nonneg_left hc.le hlB
          (hKlog hT (by simpa using hx.1) (by simp; linarith : |(0 : ℝ)| ≤ T))
  have hβ : 1 - c / Real.log (Bt (x.1 + 1) 0) ≤ ρ.re := by linarith
  have hγ : |ρ.im| ≤ c / Real.log (Bt (x.1 + 1) 0) := by rw [him, abs_zero]; positivity
  have hη31 : c / Real.log (Bt (x.1 + 1) 0) ≤ 1 / 31 := by
    rw [div_le_iff₀ hlB]
    have hh := one_le_log_Bt (N := x.1 + 1) 0
    nlinarith
  have hm := mem_Tset_of_box hχ hη31 hz hβ hγ
  classical
  have hmem : ρ - 3 / 2 ∈ (Tset hχ 0).filter (fun w =>
      1 - c / Real.log (Bt (x.1 + 1) 0) ≤ w.re + 3 / 2 ∧
      |w.im| ≤ c / Real.log (Bt (x.1 + 1) 0)) := by
    refine Finset.mem_filter.mpr ⟨hm, ?_, ?_⟩
    · have he : (ρ - 3 / 2).re + 3 / 2 = ρ.re := by simp
      rw [he]
      exact hβ
    · have he : (ρ - 3 / 2).im = ρ.im := by simp
      rw [he]
      exact hγ
  have hu : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) ≤ 1 :=
    (Finset.single_le_sum (fun w _ => Nat.zero_le _) hmem).trans (hcount (x.1 + 1) x.2 hχ)
  have hzshift : fShift x.2 0 (ρ - 3 / 2) = 0 := by simpa [fShift] using hz
  have ho : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) = 1 :=
    Nat.le_antisymm hu (one_le_order hχ 0 hzshift)
  have hg : AnalyticAt ℂ (fun z : ℂ => z + 3 / 2) (ρ - 3 / 2) := by fun_prop
  have hd : deriv (fun z : ℂ => z + 3 / 2) (ρ - 3 / 2) ≠ 0 := by simp
  have hshift := analyticOrderAt_comp_of_deriv_ne_zero (f := x.2.LFunction) hg hd
  have hnat := congrArg ENat.toNat hshift
  have he : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) =
      analyticOrderNatAt x.2.LFunction ρ := by
    unfold analyticOrderNatAt
    have hf : fShift x.2 0 = fun z : ℂ => x.2.LFunction (z + 3 / 2) := by
      funext z
      simp [fShift]
    rw [hf]
    simpa only [Function.comp_def, sub_add_cancel] using hnat
  exact he.symm.trans ho

/-- Gallagher 1975 p.127. The exceptional conductor exceeds every fixed power of log T
up to a positive constant depending on that power. No effective constant is asserted. -/
theorem exceptional_conductor_log_growth : ∃ b : ℝ, 0 < b ∧
    ∀ B : ℝ, 0 < B → ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ x ∈ excSet b T, c * Real.log T ^ B ≤ (x.1 : ℝ) + 1 := by
  obtain ⟨b, hb, hreal⟩ := page_real
  refine ⟨b, hb, ?_⟩
  intro B hB
  obtain ⟨cs, hcs, hs⟩ := siegel (1 / B) (by positivity)
  refine ⟨(cs / b) ^ B, Real.rpow_pos_of_pos (div_pos hcs hb) _, ?_⟩
  intro T hT x hx
  obtain ⟨ρ, hz, hβ, ht⟩ := hx.2.2
  have hchi := (hreal T hT x hx).1
  have him := (hreal T hT x hx).2 ρ hz hβ ht
  have he : (ρ.re : ℂ) = ρ := by apply Complex.ext <;> simp [him]
  have hzreal : x.2.LFunction (ρ.re : ℂ) = 0 := by rwa [he]
  have hS := hs x.1 x.2 hx.2.1 hchi ρ.re hzreal
  let r : ℝ := (x.1 : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hbound : cs * r ^ (-(1 / B)) ≤ b / Real.log T := by
    dsimp [r]
    linarith
  rw [Real.rpow_neg hr.le, ← div_eq_mul_inv] at hbound
  have hp : 0 < r ^ (1 / B) := Real.rpow_pos_of_pos hr _
  have hprod := (div_le_div_iff₀ hp hlT).mp hbound
  have hbase : cs / b * Real.log T ≤ r ^ (1 / B) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb]
    nlinarith
  have hraise := Real.rpow_le_rpow (by positivity : 0 ≤ cs / b * Real.log T) hbase hB.le
  rw [← Real.rpow_mul hr.le, one_div_mul_cancel hB.ne', Real.rpow_one] at hraise
  rw [Real.mul_rpow (div_nonneg hcs.le hb.le) hlT.le] at hraise
  exact hraise

/-- Gallagher 1975 pp.127 and 131. The entire primitive family has at most one counted zero in a fixed Page strip. -/
theorem density_sum_in_page_strip : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ σ : ℝ, 1 - b / Real.log T ≤ σ →
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          (zeroCount χ σ T : ℝ) ≤ 1 := by
  classical
  obtain ⟨bc, hbc, hchar⟩ := page_subsingleton
  obtain ⟨bz, hbz, hzero⟩ := page_zero_unique
  let b := min bc bz
  have hb : 0 < b := lt_min hbc hbz
  refine ⟨b, hb, fun T hT σ hσ => ?_⟩
  let chars (q : ℕ) := (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive)
  let S := (range ⌊T⌋₊).sigma chars
  have hprim (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S) : x.2.IsPrimitive :=
    (mem_filter.mp (mem_sigma.mp hx).2).2
  have hqT (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S) : (x.1 : ℝ) + 1 ≤ T := by
    have hq : x.1 < ⌊T⌋₊ := mem_range.mp (mem_sigma.mp hx).1
    have hh : ((x.1 + 1 : ℕ) : ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast (by omega : x.1 + 1 ≤ ⌊T⌋₊)
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ T by linarith)
    push_cast at hh
    exact hh.trans hfloor
  have hmem (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S)
      (hc : zeroCount x.2 σ T ≠ 0) : x ∈ excSet b T := by
    have hne : {ρ : ℂ | x.2.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} ≠ ∅ := by
      intro he
      apply hc
      simp only [zeroCount, he, Set.ncard_empty]
    obtain ⟨ρ, hz, hβ, ht⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact ⟨hqT x hx, hprim x hx, ρ, hz, hσ.trans hβ, ht⟩
  have hcount (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hx : x ∈ S) : zeroCount x.2 σ T ≤ 1 := by
    by_cases hc : zeroCount x.2 σ T = 0
    · omega
    have hxE := excSet_mono (min_le_right bc bz) hT (hmem x hx hc)
    have hσz : 1 - bz / Real.log T ≤ σ := by
      have hd := div_le_div_of_nonneg_right (min_le_right bc bz)
        (show (0 : ℝ) ≤ Real.log T by apply Real.log_nonneg; linarith)
      dsimp [b] at hσ
      linarith
    have hsub : ({ρ : ℂ | x.2.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} : Set ℂ).Subsingleton := by
      intro ρ₁ hρ₁ ρ₂ hρ₂
      exact hzero T hT x hxE ρ₁ ρ₂ hρ₁.1 hρ₂.1
        (hσz.trans hρ₁.2.1) hρ₁.2.2 (hσz.trans hρ₂.2.1) hρ₂.2.2
    exact (Set.ncard_le_one hsub.finite).mpr (fun a ha b hb => hsub ha hb)
  let I := S.filter (fun x => zeroCount x.2 σ T ≠ 0)
  have hI : I.card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS, hxc⟩ := mem_filter.mp hx
    obtain ⟨hyS, hyc⟩ := mem_filter.mp hy
    exact hchar T hT (excSet_mono (min_le_left bc bz) hT (hmem x hxS hxc))
      (excSet_mono (min_le_left bc bz) hT (hmem y hyS hyc))
  have heq : (∑ x ∈ I, (zeroCount x.2 σ T : ℝ)) = ∑ x ∈ S, (zeroCount x.2 σ T : ℝ) := by
    apply sum_subset (filter_subset _ _)
    intro x hx hxI
    have hc : zeroCount x.2 σ T = 0 := by
      by_contra hn
      exact hxI (mem_filter.mpr ⟨hx, hn⟩)
    simp [hc]
  calc
    _ = ∑ x ∈ S, (zeroCount x.2 σ T : ℝ) := sum_sigma' _ _ _
    _ = ∑ x ∈ I, (zeroCount x.2 σ T : ℝ) := heq.symm
    _ ≤ ∑ _x ∈ I, (1 : ℝ) := by
      apply sum_le_sum
      intro x hx
      exact_mod_cast hcount x (mem_filter.mp hx).1
    _ = (I.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hI

/-- Gallagher 1975 p.131. Auxiliary total count from the proved unit height estimate.
The constant is uniform in the primitive character, real part and height. -/
theorem zeroCount_le_unit_height : ∃ A : ℝ, 0 ≤ A ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ σ T : ℝ, 1 / 2 ≤ σ → 0 ≤ T →
      (zeroCount χ σ T : ℝ) ≤ (⌊T⌋₊ + 1 : ℕ) * A * Real.log (q * (T + 2)) := by
  obtain ⟨A, hA, huall⟩ := LeanLab.HardyLittlewood1923.U1482.zeroCountUnit
  refine ⟨A, hA, fun q _ χ hp σ T hσ hT => ?_⟩
  have hu := huall q χ hp
  classical
  let W : ℕ → Finset ℂ := fun j => (hu j (Nat.cast_nonneg _)).1.toFinset
  have hψ : q = 1 ∨ χ ≠ 1 := by
    by_cases hq : q = 1
    · exact Or.inl hq
    · right
      intro hχ
      apply hq
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hh
      exact hh.symm
  have hnt {ρ : ℂ} (hz : χ.LFunction ρ = 0) (hβ : σ ≤ ρ.re) :
      LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ := by
    refine ⟨hz, by linarith, ?_⟩
    by_contra h
    have hre : 1 ≤ ρ.re := le_of_not_gt h
    rcases hψ with rfl | hχ
    · rw [DirichletCharacter.LFunction_modOne_eq] at hz
      exact riemannZeta_ne_zero_of_one_le_re hre hz
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre hz
  have horder {ρ : ℂ} (hρ : LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ) :
      1 ≤ LeanLab.HardyLittlewood1923.U1479.mult χ ρ := by
    have hw : ρ ≠ 1 := by
      intro he
      have hh := hρ.2.2
      simp [he] at hh
    have hz : analyticOrderNatAt χ.LFunction ρ ≠ 0 := by
      simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(LeanLab.HardyLittlewood1923.U1482.L_analyticAt χ hw).analyticOrderAt_ne_zero.mpr hρ.1,
        LeanLab.HardyLittlewood1923.U1482.L_ord_ne_top χ hψ hw⟩
    change (1 : ℝ) ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hcard (j : ℕ) : ((W j).card : ℝ) ≤ A * Real.log (q * ((j : ℝ) + 2)) := by
    have hmem (ρ : ℂ) (hρ : ρ ∈ W j) :
        LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ ∧
          (j : ℝ) ≤ |ρ.im| ∧ |ρ.im| ≤ (j : ℝ) + 1 := by
      simpa only [W, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hρ
    calc
      _ = ∑ _ρ ∈ W j, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ W j, LeanLab.HardyLittlewood1923.U1479.mult χ ρ :=
        sum_le_sum (fun ρ hρ => horder (hmem ρ hρ).1)
      _ ≤ _ := (hu j (Nat.cast_nonneg _)).2 (W j) hmem
  let U : Finset ℂ := (range (⌊T⌋₊ + 1)).biUnion W
  have hsub : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} ⊆ (U : Set ℂ) := by
    intro ρ hρ
    have hj : ⌊|ρ.im|⌋₊ < ⌊T⌋₊ + 1 := by
      have := Nat.floor_mono hρ.2.2
      omega
    apply mem_biUnion.mpr
    refine ⟨⌊|ρ.im|⌋₊, mem_range.mpr hj, ?_⟩
    simp only [W, Set.Finite.mem_toFinset]
    exact ⟨hnt hρ.1 hρ.2.1, Nat.floor_le (abs_nonneg _), (Nat.lt_floor_add_one _).le⟩
  have hc : zeroCount χ σ T ≤ U.card := by
    simpa only [zeroCount, Set.ncard_coe_finset] using Set.ncard_le_ncard hsub U.finite_toSet
  calc
    _ ≤ (U.card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ j ∈ range (⌊T⌋₊ + 1), ((W j).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ j ∈ range (⌊T⌋₊ + 1), A * Real.log (q * (T + 2)) := by
      apply sum_le_sum
      intro j hj
      have hjT : (j : ℝ) ≤ T :=
        (show (j : ℝ) ≤ ⌊T⌋₊ by exact_mod_cast (by have := mem_range.mp hj; omega : j ≤ ⌊T⌋₊)).trans
          (Nat.floor_le hT)
      apply (hcard j).trans
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.log_le_log (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) (by positivity))
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = _ := by simp; ring

/-- Gallagher 1975 p.131. Auxiliary polynomial bound for the whole primitive family.
This uses the proved unit height count and no density estimate. -/
theorem density_sum_polynomial : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (4 : ℕ) := by
  classical
  obtain ⟨A, hA, hu⟩ := zeroCount_le_unit_height
  refine ⟨4 * A, by positivity, fun T hT σ hσ => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hK : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T := by
    have := Nat.floor_le hT0
    push_cast
    linarith
  have hsingle (q : ℕ) (hq : q ∈ range ⌊T⌋₊)
      (χ : DirichletCharacter ℂ (q + 1)) (hp : χ.IsPrimitive) :
      (zeroCount χ σ T : ℝ) ≤ 4 * A * T ^ 2 := by
    have hqT : ((q + 1 : ℕ) : ℝ) ≤ T := by
      have hn : q + 1 ≤ ⌊T⌋₊ := by have := mem_range.mp hq; omega
      exact (show ((q + 1 : ℕ) : ℝ) ≤ ⌊T⌋₊ by exact_mod_cast hn).trans (Nat.floor_le hT0)
    have hlog : Real.log ((q + 1 : ℕ) * (T + 2)) ≤ 2 * T := by
      calc
        _ ≤ Real.log (T * (T + 2)) :=
          Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hqT (by positivity))
        _ = Real.log T + Real.log (T + 2) :=
          Real.log_mul hTpos.ne' (by positivity)
        _ ≤ (T - 1) + (T + 2 - 1) := add_le_add
          (Real.log_le_sub_one_of_pos hTpos) (Real.log_le_sub_one_of_pos (by positivity))
        _ = 2 * T := by ring
    have hlog0 : 0 ≤ Real.log ((q + 1 : ℕ) * (T + 2)) := by
      apply Real.log_nonneg
      have hq1 : (1 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ q + 1)
      have hmul := mul_le_mul_of_nonneg_right hq1 (show 0 ≤ T + 2 by linarith)
      nlinarith
    calc
      _ ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) * A * Real.log ((q + 1 : ℕ) * (T + 2)) :=
        hu (q + 1) χ hp σ T hσ hT0
      _ ≤ (2 * T) * A * (2 * T) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hK hA) hlog hlog0 (by positivity)
      _ = _ := by ring
  have hfamily (q : ℕ) (hq : q ∈ range ⌊T⌋₊) :
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ)) ≤ T * (4 * A * T ^ 2) := by
    let S := (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive)
    have hcard : (S.card : ℝ) ≤ T := by
      have hc : S.card ≤ (q + 1).totient := by
        calc
          S.card ≤ Fintype.card (DirichletCharacter ℂ (q + 1)) := card_le_univ _
          _ = (q + 1).totient := by
            rw [← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      have hn : q + 1 ≤ ⌊T⌋₊ := by have := mem_range.mp hq; omega
      exact (show (S.card : ℝ) ≤ ⌊T⌋₊ by
        exact_mod_cast hc.trans ((Nat.totient_le _).trans hn)).trans (Nat.floor_le hT0)
    calc
      _ ≤ ∑ _χ ∈ S, (4 * A * T ^ 2) :=
        sum_le_sum (fun χ hχ => hsingle q hq χ (mem_filter.mp hχ).2)
      _ = (S.card : ℝ) * (4 * A * T ^ 2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  calc
    _ ≤ ∑ _q ∈ range ⌊T⌋₊, T * (4 * A * T ^ 2) := sum_le_sum hfamily
    _ = (⌊T⌋₊ : ℝ) * (T * (4 * A * T ^ 2)) := by simp
    _ ≤ T * (T * (4 * A * T ^ 2)) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hT0) (by positivity)
    _ = _ := by ring


/-- Gallagher 1975 p.131. The region at most three quarters needs no density theorem. -/
theorem density_sum_away_from_one : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (16 * (1 - σ)) := by
  obtain ⟨C, hC, h⟩ := density_sum_polynomial
  refine ⟨C, hC, fun T hT σ hσ hσ' => (h T hT σ hσ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num at *; linarith)

/-- Gallagher 1970 p.335, reduction before Theorem 6. The polynomial count proves
any region with a fixed positive horizontal gap. The exponent is explicit in the gap. -/
theorem density_sum_fixed_gap (η : ℝ) (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 - η →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ ((4 / η) * (1 - σ)) := by
  obtain ⟨C, hC, h⟩ := density_sum_polynomial
  refine ⟨C, hC, fun T hT σ hσ hgap => (h T hT σ hσ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ hη]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Finite interpolation identity behind Gallagher 1970 p.334, Turan step. -/
theorem power_sum_interpolation {n : ℕ} (z a b : Fin n → ℂ) (M : ℕ) :
    (∑ j, b j * ∑ i, a i * z i ^ (M + 1 + j.val)) =
      ∑ i, a i * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val := by
  simp only [Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [pow_add]
  ring



open scoped Classical
/-- Nonzero interpolation data force a nonzero power sum in the next n powers. -/
theorem power_sum_nonzero_of_injective {n : ℕ} (z a : Fin n → ℂ) (M : ℕ)
    (hz : Function.Injective z) (ha : ∃ i, a i ≠ 0 ∧ z i ≠ 0) :
    ∃ j : Fin n, (∑ i, a i * z i ^ (M + 1 + j.val)) ≠ 0 := by
  by_contra h
  push Not at h
  have hv : (fun i => a i * z i ^ (M + 1)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hz
    intro j
    simpa only [pow_add, mul_assoc] using h j
  obtain ⟨i, hai, hzi⟩ := ha
  have := congr_fun hv i
  exact (mul_ne_zero hai (pow_ne_zero _ hzi)) this


/-- The interpolation coefficient norm controls the largest power sum. -/
theorem power_sum_interpolation_bound {n : ℕ} (z a b : Fin n → ℂ) (M : ℕ)
    {B : ℝ} (hB : ∀ j : Fin n, ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ ≤ B) :
    ‖∑ i, a i * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val‖ ≤
      (∑ j, ‖b j‖) * B := by
  rw [← power_sum_interpolation]
  calc
    _ ≤ ∑ j, ‖b j * ∑ i, a i * z i ^ (M + 1 + j.val)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖b j‖ * B := by
      apply sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB j) (norm_nonneg _)
    _ = _ := (sum_mul ..).symm


/-- A bounded interpolant supplies a quantitative power sum lower bound. -/
theorem power_sum_lower_bound_of_interpolant {n : ℕ} (hn : 0 < n)
    (z a b : Fin n → ℂ) (M : ℕ) {A B : ℝ} (hB : 0 < B)
    (hcoeff : (∑ j, ‖b j‖) ≤ B)
    (hvalue : A ≤ ‖∑ i, a i * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val‖) :
    ∃ j : Fin n, A / B ≤ ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, _, hj⟩ := exists_max_image (univ : Finset (Fin n))
    (fun j => ‖∑ i, a i * z i ^ (M + 1 + j.val)‖) univ_nonempty
  refine ⟨j, (div_le_iff₀ hB).mpr ?_⟩
  calc
    A ≤ _ := hvalue
    _ ≤ (∑ j, ‖b j‖) * ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ :=
      power_sum_interpolation_bound z a b M (fun k => hj k (mem_univ k))
    _ ≤ B * ‖∑ i, a i * z i ^ (M + 1 + j.val)‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ = _ := mul_comm _ _


/-- The pure single term Turan bound has no cancellation. -/
theorem turan_power_sum_single {z : ℂ} (hz : 1 ≤ ‖z‖) (M : ℕ) (hM : 1 ≤ M) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖z ^ ν‖ := by
  refine ⟨M + 1, by omega, by omega, ?_⟩
  calc
    (1 / 50 : ℝ) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    _ ≤ ‖z ^ (M + 1)‖ := by rw [norm_pow]; exact one_le_pow₀ hz


/-- Repeated roots are combined with their positive multiplicities.
Qualitative finite part of Gallagher 1970 p.334, with no separation assumption. -/
theorem pure_power_sum_nonzero {n : ℕ} (z : Fin n → ℂ) (M : ℕ)
    (hz : ∃ i, z i ≠ 0) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ M + n ∧ (∑ i, z i ^ ν) ≠ 0 := by
  classical
  let s : Finset ℂ := univ.image z
  let LeanLab.PNTPort.LargeSieve.e : Fin s.card ≃ ↥s := s.equivFin.symm
  let v : Fin s.card → ℂ := fun i => (LeanLab.PNTPort.LargeSieve.e i).val
  let a : Fin s.card → ℂ := fun j => ((univ.filter (fun i => z i = v j)).card : ℂ)
  have hv : Function.Injective v := by
    intro i j hij
    apply LeanLab.PNTPort.LargeSieve.e.injective
    exact Subtype.ext hij
  have hsum (k : ℕ) : (∑ j, a j * v j ^ k) = ∑ i, z i ^ k := by
    calc
      _ = ∑ u : ↥s, ((univ.filter (fun i => z i = u.val)).card : ℂ) * u.val ^ k :=
        LeanLab.PNTPort.LargeSieve.e.sum_comp _
      _ = ∑ u ∈ s, ((univ.filter (fun i => z i = u)).card : ℂ) * u ^ k :=
        sum_coe_sort s (fun u : ℂ =>
          (((univ : Finset (Fin n)).filter (fun i => z i = u)).card : ℂ) * u ^ k)
      _ = ∑ u ∈ s, ∑ i ∈ univ.filter (fun i => z i = u), z i ^ k := by
        apply sum_congr rfl
        intro u _
        rw [show (∑ i ∈ univ.filter (fun i => z i = u), z i ^ k) =
            ∑ _i ∈ univ.filter (fun i => z i = u), u ^ k from
          sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2])]
        simp
      _ = _ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem z hi) _
  have ha : ∃ j, a j ≠ 0 ∧ v j ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    have hzi : z i ∈ s := mem_image_of_mem z (mem_univ i)
    let j := LeanLab.PNTPort.LargeSieve.e.symm ⟨z i, hzi⟩
    have hj : v j = z i := by simp [v, j]
    refine ⟨j, ?_, hj ▸ hi⟩
    dsimp [a]
    apply Nat.cast_ne_zero.mpr
    apply card_ne_zero.mpr
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hj.symm⟩⟩
  obtain ⟨j, hj⟩ := power_sum_nonzero_of_injective v a M hv ha
  have hcard : s.card ≤ n := by
    exact (card_image_le).trans (by simp)
  refine ⟨M + 1 + j.val, by omega, by have := j.isLt; omega, ?_⟩
  rwa [hsum] at hj


/-- Compactness gives a uniform lower bound at each fixed length and starting power.
This does not supply the exponential constant required by Turan's theorem. -/
theorem pure_power_sum_fixed_length {n : ℕ} (hn : 0 < n) (M : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin n → ℂ, ‖z‖ = 1 →
      ∃ ν : ℕ, M < ν ∧ ν ≤ M + n ∧ ε ≤ ‖∑ i, z i ^ ν‖ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let F : (Fin n → ℂ) → ℝ := fun z => ∑ j : Fin n, ‖∑ i, z i ^ (M + 1 + j.val)‖
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hpos (z : Fin n → ℂ) (hz : ‖z‖ = 1) : 0 < F z := by
    have hne : z ≠ 0 := by intro he; simp [he] at hz
    have hex : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨ν, hνM, hνn, hν⟩ := pure_power_sum_nonzero z M hex
    let j : Fin n := ⟨ν - (M + 1), by omega⟩
    have hj : M + 1 + j.val = ν := by dsimp [j]; omega
    have hle : ‖∑ i, z i ^ ν‖ ≤ F z := by
      dsimp [F]
      rw [← hj]
      exact single_le_sum (fun k _ => norm_nonneg (∑ i, z i ^ (M + 1 + k.val))) (mem_univ j)
    exact (norm_pos_iff.mpr hν).trans_le hle
  have hs : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨z₀, hz₀, hmin⟩ := hs.exists_isMinOn hne hF.continuousOn
  have hz₀norm : ‖z₀‖ = 1 := by simpa using hz₀
  have hε : 0 < F z₀ / (n : ℝ) := div_pos (hpos z₀ hz₀norm) (by exact_mod_cast hn)
  refine ⟨F z₀ / n, hε, ?_⟩
  intro z hz
  obtain ⟨j, _, hj⟩ := exists_max_image (univ : Finset (Fin n))
    (fun j => ‖∑ i, z i ^ (M + 1 + j.val)‖) univ_nonempty
  refine ⟨M + 1 + j.val, by omega, by have := j.isLt; omega, ?_⟩
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  have hlow : F z₀ ≤ F z := hmin (by simpa using hz)
  have hu : F z ≤ (n : ℝ) * ‖∑ i, z i ^ (M + 1 + j.val)‖ := by
    calc
      F z ≤ ∑ _k : Fin n, ‖∑ i, z i ^ (M + 1 + j.val)‖ :=
        sum_le_sum (fun k _ => hj k (mem_univ k))
      _ = _ := by simp
  nlinarith


/-- A singleton selector has unbounded coefficients as two roots coalesce.
This is a limitation of a fixed singleton interpolation route to Gallagher p.334. -/
theorem singleton_selector_unbounded (B : ℝ) (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ b₀ b₁ : ℂ, b₀ + b₁ = 1 → b₀ + (r : ℂ) * b₁ = 0 → B < ‖b₁‖ := by
  let d : ℝ := 1 / (B + 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by dsimp [d]; rw [div_lt_one (by linarith)]; linarith
  have hdB : d * (B + 2) = 1 := by dsimp [d]; field_simp
  refine ⟨1 - d, by linarith, by linarith, ?_⟩
  intro b₀ b₁ h₀ h₁
  have he : (d : ℂ) * b₁ = 1 := by
    push_cast at h₁
    linear_combination h₀ - h₁
  have hn := congrArg norm he
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, norm_one] at hn
  nlinarith


/-- Quantitative two root auxiliary for the finite Turan step on Gallagher p.334.
It handles cancellation for one unit root and a second root in the closed unit disc. -/
theorem two_term_power_sum_bound (w : ℂ) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    1 / (4 * (k : ℝ) + 4) ≤ ‖1 + w ^ k‖ ∨
      1 / (4 * (k : ℝ) + 4) ≤ ‖1 + w ^ (k + 1)‖ := by
  let d : ℝ := 1 / (4 * (k : ℝ) + 4)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd4 : d ≤ 1 / 4 := by dsimp [d]; apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hdc : (4 * (k : ℝ) + 4) * d = 1 := by dsimp [d]; field_simp
  by_contra h
  push Not at h
  change ‖1 + w ^ k‖ < d ∧ ‖1 + w ^ (k + 1)‖ < d at h
  have hwp : (1 / 2 : ℝ) ≤ ‖w ^ k‖ := by
    have ht := norm_sub_le (1 + w ^ k) (w ^ k)
    simp only [add_sub_cancel_right, norm_one] at ht
    linarith [h.1]
  have hdiff : ‖w ^ k‖ * ‖w - 1‖ < 2 * d := by
    rw [← norm_mul]
    have he : w ^ k * (w - 1) = (1 + w ^ (k + 1)) - (1 + w ^ k) := by
      rw [pow_succ]; ring
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith [h.1, h.2])
  have hnear : ‖1 - w‖ < 4 * d := by
    rw [norm_sub_rev]
    nlinarith [mul_le_mul_of_nonneg_right hwp (norm_nonneg (w - 1))]
  have hsum : ‖∑ j ∈ range k, w ^ j‖ ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ j ∈ range k, ‖w ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range k, (1 : ℝ) := by
        apply sum_le_sum
        intro j _
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := by simp
  have htel : ‖1 - w ^ k‖ ≤ (k : ℝ) * ‖1 - w‖ := by
    rw [← geom_sum_mul_neg w k, norm_mul]
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have ht := norm_add_le (1 + w ^ k) (1 - w ^ k)
  have he : (1 + w ^ k) + (1 - w ^ k) = (2 : ℂ) := by ring
  rw [he] at ht
  norm_num only [Complex.norm_ofNat] at ht
  have hh := mul_le_mul_of_nonneg_left hnear.le (Nat.cast_nonneg k)
  nlinarith [h.1]


/-- The two root Turan bound with the explicit constant used on Gallagher p.334.
This finite case includes cancellation. The general finite interpolation leaf remains separate. -/
theorem turan_power_sum_pair (z w : ℂ) (hz : 1 ≤ ‖z‖) (hw : ‖w‖ ≤ ‖z‖)
    (M : ℕ) (hM : 2 ≤ M) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖z ^ ν + w ^ ν‖ := by
  have hz0 : z ≠ 0 := by intro he; norm_num [he] at hz
  have hr : ‖w / z‖ ≤ 1 := by rw [norm_div, div_le_one (by linarith : 0 < ‖z‖)]; exact hw
  have hp : ∀ m : ℕ, 1 ≤ m → 4 * (m : ℝ) + 8 ≤ (50 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m; norm_num
      · have hprev := ih (by omega)
        rw [pow_succ]
        push_cast
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 50) m]
  have hsmall : (1 / 50 : ℝ) ^ M ≤ 1 / (4 * ((M + 1 : ℕ) : ℝ) + 4) := by
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    have := hp M (by omega)
    push_cast
    linarith
  have hscale (ν : ℕ) : ‖1 + (w / z) ^ ν‖ ≤ ‖z ^ ν + w ^ ν‖ := by
    have he : z ^ ν + w ^ ν = z ^ ν * (1 + (w / z) ^ ν) := by
      rw [div_pow]
      field_simp
    rw [he, norm_mul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hz)
  rcases two_term_power_sum_bound (w / z) hr (M + 1) with h | h
  · exact ⟨M + 1, by omega, by omega, hsmall.trans (h.trans (hscale _))⟩
  · exact ⟨M + 2, by omega, by omega, hsmall.trans (h.trans (hscale _))⟩


/-- LEAF. Finite interpolation construction in Turan's second power sum theorem.
Gallagher 1970 p.334 after display 21. Vaughan author notes, Vol.3 pp.351 to 353,
proof of Theorem K.3. Corollary K.5 and 16e less than 50 give this coefficient bound.
No L-function or analytic number theory assumption occurs in this finite statement. -/
theorem turan_interpolant {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hunit : ∃ i, ‖z i‖ = 1) :
    ∃ J : Finset (Fin n), J.Nonempty ∧ ∃ b : Fin n → ℂ,
      (∀ i, z i ^ (M + 1) * (∑ j, b j * z i ^ j.val) = if i ∈ J then 1 else 0) ∧
      (∑ j, ‖b j‖) ≤ (50 : ℝ) ^ M := by
  sorry


/-- Turan's finite lower bound used in Gallagher 1970 p.334.
CONDITIONAL ON the finite interpolation construction turan_interpolant. -/
theorem turan_power_sum_lower_bound_normalized {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (hunit : ∃ i, ‖z i‖ = 1) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖ := by
  classical
  obtain ⟨J, hJ, b, hbi, hb⟩ := turan_interpolant hn hnM z hz hunit
  have hv : (1 : ℝ) ≤ ‖∑ i, (1 : ℂ) * z i ^ (M + 1) * ∑ j, b j * z i ^ j.val‖ := by
    simp_rw [one_mul, hbi]
    simp only [sum_ite_mem, sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
    simp only [univ_inter]
    exact_mod_cast (Nat.succ_le_iff.mpr hJ.card_pos)
  obtain ⟨j, hj⟩ := power_sum_lower_bound_of_interpolant hn z (fun _ => 1) b M
    (by positivity : (0 : ℝ) < 50 ^ M) hb hv
  refine ⟨M + 1 + j.val, by omega, by have := j.isLt; omega, ?_⟩
  simpa only [one_mul, div_pow, one_pow] using hj


/-- General pure power sum form of the Turan input on Gallagher 1970 p.334.
CONDITIONAL ON turan_interpolant. Normalizing the largest root costs no lower bound. -/
theorem turan_power_sum_lower_bound {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (z : Fin n → ℂ) (hz : ∃ i, 1 ≤ ‖z i‖) :
    ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, _, hi⟩ := exists_max_image (univ : Finset (Fin n)) (fun j => ‖z j‖) univ_nonempty
  let R : ℝ := ‖z i‖
  have hR1 : 1 ≤ R := by
    obtain ⟨j, hj⟩ := hz
    exact hj.trans (hi j (mem_univ j))
  have hR : 0 < R := by linarith
  let w : Fin n → ℂ := fun j => z j / (R : ℂ)
  have hwnorm (j : Fin n) : ‖w j‖ = ‖z j‖ / R := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hw : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    rw [hwnorm, div_le_one hR]
    exact hi j (mem_univ j)
  have hwi : ∃ j, ‖w j‖ = 1 := ⟨i, by rw [hwnorm]; exact div_self hR.ne'⟩
  obtain ⟨ν, hνM, hν2, hν⟩ := turan_power_sum_lower_bound_normalized hn hnM w hw hwi
  refine ⟨ν, hνM, hν2, hν.trans ?_⟩
  have hsum : (∑ j, w j ^ ν) = (∑ j, z j ^ ν) / (R : ℂ) ^ ν := by
    dsimp [w]
    simp_rw [div_pow]
    exact (sum_div ..).symm
  rw [hsum, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hpow : 1 ≤ R ^ ν := one_le_pow₀ hR1
  rw [div_le_iff₀ (by positivity : 0 < R ^ ν)]
  nlinarith [mul_le_mul_of_nonneg_left hpow (norm_nonneg (∑ j, z j ^ ν))]


open FourierTransform
open LeanLab.Linnik.U1394Fejer
/-- Fourier inversion for the Fejer kernel used in Gallagher 1970 p.330. -/
theorem integral_fejer_exp (x : ℝ) :
    ∫ t : ℝ, LeanLab.PNTPort.LargeSieve.e (x * t) * (fej t : ℂ) = (tri x : ℂ) := by
  have hF : 𝓕 (fun u => (tri u : ℂ)) = fun t => (fej t : ℂ) := by
    funext t
    rw [fourier_tri, fej_eq_G]
  have hFi : Integrable (𝓕 (fun u => (tri u : ℂ))) := by
    rw [hF]
    exact integrable_fej.ofReal
  have hi := integrable_tri.fourierInv_fourier_eq hFi
    ((Complex.continuous_ofReal.comp continuous_tri).continuousAt (x := x))
  rw [Real.fourierInv_eq', hF] at hi
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Real.inner_apply, smul_eq_mul]
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 2
  push_cast
  ring


/-- The scaled Fourier kernel for Gallagher 1970 p.330 Lemma 1. -/
theorem integral_fejer_exp_scaled (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t : ℝ, LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ) = (δ⁻¹ * tri (x / δ) : ℝ) := by
  have heq : (fun t : ℝ => LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ)) =
      fun t => (fun u => LeanLab.PNTPort.LargeSieve.e ((x / δ) * u) * (fej u : ℂ)) (δ * t) := by
    ext t
    congr 2
    field_simp
  rw [heq, Measure.integral_comp_mul_left (fun u : ℝ => LeanLab.PNTPort.LargeSieve.e ((x / δ) * u) * (fej u : ℂ)) δ, integral_fejer_exp]
  simp only [abs_of_pos (inv_pos.mpr hδ), Complex.real_smul, Complex.ofReal_mul]


/-- Integrability of the phase times Fejer weight. -/
theorem integrable_fejer_phase (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ)) := by
  have hi := integrable_fej.comp_mul_left' hδ.ne'
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
    · exact Complex.continuous_ofReal.comp (continuous_fej.comp (continuous_const.mul continuous_id))
  · filter_upwards [] with t
    rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fej_nonneg _)]


/-- Exact smoothed Fourier energy for any finite real frequency family. -/
theorem fejer_exponential_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ) (freq : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ((∫ t : ℝ, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) : ℝ) : ℂ) =
      (δ⁻¹ : ℂ) * ∑ i ∈ s, ∑ j ∈ s,
        a i * (starRingEnd ℂ) (a j) * (tri ((freq i - freq j) / δ) : ℂ) := by
  have heq (t : ℝ) : ((‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i * (starRingEnd ℂ) (a j) * (LeanLab.PNTPort.LargeSieve.e ((freq i - freq j) * t) * (fej (δ * t) : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum,
      sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    rw [map_mul, ← LeanLab.PNTPort.LargeSieve.e_neg]
    rw [show (freq i - freq j) * t = freq i * t + -(freq j * t) by ring, e_add]
    ring
  rw [← integral_complex_ofReal]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (integrable_fejer_phase (freq i - freq j) hδ).const_mul _)), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (integrable_fejer_phase (freq i - freq j) hδ).const_mul _),
    mul_sum]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_fejer_exp_scaled _ hδ]
  push_cast
  ring


/-- The Fejer weight has an explicit positive lower bound near zero. -/
theorem fejer_lower_half {u : ℝ} (hu : |u| ≤ 1 / 2) : 4 / Real.pi ^ 2 ≤ fej u := by
  by_cases hz : u = 0
  · subst u
    have h0 : fej 0 = 1 := by simp [fej, LeanLab.PNTPort.LargeSieve.e]
    rw [h0, div_le_one (by positivity : (0 : ℝ) < Real.pi ^ 2)]
    nlinarith [Real.pi_gt_three]
  · have hs := LeanLab.PNTPort.LargeSieve.two_abs_le_abs_sin hu
    have hs2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * |u|) hs 2
    simp only [mul_pow, sq_abs] at hs2
    rw [fej_ne hz, le_div_iff₀ (by positivity : (0 : ℝ) < (Real.pi * u) ^ 2)]
    calc
      4 / Real.pi ^ 2 * (Real.pi * u) ^ 2 = 4 * u ^ 2 := by field_simp
      _ ≤ _ := by norm_num at hs2; exact hs2


/-- Integrability of a finite Fourier energy with Fejer weight. -/
theorem integrable_fejer_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) := by
  have hsum (t : ℝ) : ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ≤ ∑ i ∈ s, ‖a i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, norm_e, mul_one]
  have hi := (integrable_fej.comp_mul_left' hδ.ne').const_mul ((∑ i ∈ s, ‖a i‖) ^ 2)
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
    · exact continuous_fej.comp (continuous_const.mul continuous_id)
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (fej_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hsum t) 2) (fej_nonneg _)


/-- Finite frequency form of the smoothing step in Gallagher 1970 p.330 Lemma 1.
The triangle quadratic form is exactly the short interval energy kernel. -/
theorem gallagher_frequency_smoothing {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 2) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2) ≤
      (Real.pi ^ 2 / (4 * δ)) *
        (∑ i ∈ s, ∑ j ∈ s, a i * (starRingEnd ℂ) (a j) *
          (tri ((freq i - freq j) / δ) : ℂ)).re := by
  have hc : Continuous (fun t : ℝ => ∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)) := by
    unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hw : Continuous (fun t : ℝ => ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) :=
    (hc.norm.pow 2).mul (continuous_fej.comp (continuous_const.mul continuous_id))
  have hpt (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 ≤
        (Real.pi ^ 2 / 4) * (‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) := by
    have ht' : |t| ≤ T := abs_le.mpr ht
    have hnear : |δ * t| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hδ]
      exact (mul_le_mul_of_nonneg_left ht' hδ.le).trans hδT
    have hlow := fejer_lower_half hnear
    have hone : (1 : ℝ) ≤ (Real.pi ^ 2 / 4) * fej (δ * t) := by
      calc
        1 = (Real.pi ^ 2 / 4) * (4 / Real.pi ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    have hh := mul_le_mul_of_nonneg_left hone (sq_nonneg ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖)
    nlinarith
  have he := congrArg Complex.re (fejer_exponential_energy s a freq hδ)
  simp only [← Complex.ofReal_inv, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  calc
    _ ≤ ∫ t in (-T)..T, (Real.pi ^ 2 / 4) *
        (‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) :=
      intervalIntegral.integral_mono_on (by linarith) ((hc.norm.pow 2).intervalIntegrable _ _)
        ((continuous_const.mul hw).intervalIntegrable _ _) hpt
    _ = (Real.pi ^ 2 / 4) * ∫ t in (-T)..T,
        ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (Real.pi ^ 2 / 4) * ∫ t : ℝ,
        ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact setIntegral_le_integral (integrable_fejer_energy s a freq hδ)
        (Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (fej_nonneg _)))
    _ = _ := by rw [he]; ring


/-- The real interval overlap kernel behind Gallagher 1970 p.330 Lemma 1. -/
theorem interval_window_overlap (a b δ : ℝ) (_hδ : 0 ≤ δ) :
    ∫ x : ℝ, (Set.Icc (a - δ) a).indicator (fun _ => (1 : ℝ)) x *
      (Set.Icc (b - δ) b).indicator (fun _ => (1 : ℝ)) x = max 0 (δ - |a - b|) := by
  have heq : (fun x : ℝ => (Set.Icc (a - δ) a).indicator (fun _ => (1 : ℝ)) x *
      (Set.Icc (b - δ) b).indicator (fun _ => (1 : ℝ)) x) =
      (Set.Icc (a - δ) a ∩ Set.Icc (b - δ) b).indicator (fun _ => 1) := by
    ext x
    simp only [← Set.inter_indicator_mul, one_mul]
  rw [heq, integral_indicator_const 1 (measurableSet_Icc.inter measurableSet_Icc),
    Set.Icc_inter_Icc, smul_eq_mul, mul_one, Real.volume_real_Icc]
  rw [max_comm]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right (by linarith : a - δ ≤ b - δ),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    congr 1; ring
  · rw [min_eq_right hba, max_eq_left (by linarith : b - δ ≤ a - δ),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    congr 1; ring


/-- A finite short interval sum in the frequency variable. -/
noncomputable def frequencyWindow {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (δ x : ℝ) : ℂ :=
  ∑ i ∈ s, (Set.Icc (freq i - δ) (freq i)).indicator (fun _ => a i) x


/-- Exact overlap identity for the short interval energy in Gallagher p.330. -/
theorem frequency_window_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ((∫ x : ℝ, ‖frequencyWindow s a freq δ x‖ ^ 2 : ℝ) : ℂ) =
      (δ : ℂ) * ∑ i ∈ s, ∑ j ∈ s, a i * (starRingEnd ℂ) (a j) *
        (tri ((freq i - freq j) / δ) : ℂ) := by
  let A : ι → Set ℝ := fun i => Set.Icc (freq i - δ) (freq i)
  have hAi (i j : ι) : Integrable (fun x => (A i ∩ A j).indicator
      (fun _ => a i * (starRingEnd ℂ) (a j)) x) := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_Icc.inter measurableSet_Icc)
    exact (continuous_const.integrableOn_Icc).mono_set Set.inter_subset_left
  have hpt (x : ℝ) : ((‖frequencyWindow s a freq δ x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).indicator
        (fun _ => a i * (starRingEnd ℂ) (a j)) x := by
    unfold frequencyWindow
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    change (A i).indicator (fun _ => a i) x *
      (starRingEnd ℂ) ((A j).indicator (fun _ => a j) x) = _
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;>
      simp [hi, hj, Set.indicator_of_mem, Set.indicator_of_notMem]
  have hover (i j : ι) : volume.real (A i ∩ A j) =
      δ * tri ((freq i - freq j) / δ) := by
    have hi := interval_window_overlap (freq i) (freq j) δ hδ.le
    have he : (fun x : ℝ => (A i).indicator (fun _ => (1 : ℝ)) x *
        (A j).indicator (fun _ => (1 : ℝ)) x) =
        (A i ∩ A j).indicator (fun _ => (1 : ℝ)) := by
      ext x
      simp only [← Set.inter_indicator_mul, one_mul]
    change (∫ x : ℝ, (A i).indicator (fun _ => (1 : ℝ)) x *
      (A j).indicator (fun _ => (1 : ℝ)) x) = _ at hi
    rw [he, integral_indicator_const 1 (measurableSet_Icc.inter measurableSet_Icc),
      smul_eq_mul, mul_one] at hi
    rw [hi]
    unfold tri
    rw [abs_div, abs_of_pos hδ]
    by_cases h : |freq i - freq j| ≤ δ
    · rw [max_eq_right (by linarith), max_eq_right (by
        rw [sub_nonneg, div_le_one hδ]; exact h)]
      field_simp
    · have hh : δ < |freq i - freq j| := lt_of_not_ge h
      rw [max_eq_left (by linarith), max_eq_left (by
        rw [sub_nonpos, le_div_iff₀ hδ]; linarith)]
      ring
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAi i j)), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hAi i j), mul_sum]
  apply sum_congr rfl
  intro j _
  rw [integral_indicator_const _ (measurableSet_Icc.inter measurableSet_Icc), hover]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring


/-- Gallagher 1970 p.330 Lemma 1 for a finite family, with explicit constant.
Closed frequency windows change only finitely many endpoints in the outer integral. -/
theorem gallagher_window_smoothing {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 2) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2) ≤
      (Real.pi ^ 2 / (4 * δ ^ 2)) * ∫ x : ℝ, ‖frequencyWindow s a freq δ x‖ ^ 2 := by
  have he := congrArg Complex.re (frequency_window_energy s a freq hδ)
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  have hh := gallagher_frequency_smoothing s a freq hδ hT hδT
  apply hh.trans_eq
  rw [he]
  field_simp


/-- Dropping the totient weights in Gallagher 1970 p.332 Lemma 3. -/
theorem large_sieve_unweighted
    (a : ℕ → ℂ) (M L Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + L), a n * χ n‖ ^ 2) ≤
      ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + L), ‖a n‖ ^ 2 := by
  apply le_trans _ (large_sieve a M L Q)
  apply sum_le_sum
  intro q hq
  have hq0 : 0 < q := (mem_Icc.mp hq).1
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hweight : (1 : ℝ) ≤ q / (q.totient : ℝ) := (le_div_iff₀ hφ0).mpr (by simpa using hφq)
  exact le_mul_of_one_le_left (sum_nonneg (fun _ _ => sq_nonneg _)) hweight


/-- The finite sieve applies to any subset of an integer interval. -/
theorem large_sieve_finset
    (s : Finset ℕ) (a : ℕ → ℂ) (M L Q : ℕ) (hs : s ⊆ Ioc M (M + L)) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
      ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  classical
  let b : ℕ → ℂ := fun n => if n ∈ s then a n else 0
  have hset : (Finset.Ioc M (M + L)).filter (fun n => n ∈ s) = s := by
    ext n
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun hn => hs hn)
  have hsum {q : ℕ} (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ Ioc M (M + L), b n * χ n) = ∑ n ∈ s, a n * χ n := by
    simp only [b, ite_mul, zero_mul, ← sum_filter, hset]
  have henergy : (∑ n ∈ Ioc M (M + L), ‖b n‖ ^ 2) = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    simp only [b, apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
      ← sum_filter, hset]
  simpa only [hsum, henergy] using large_sieve_unweighted b M L Q


/-- Real endpoints cost at most two extra integers in the finite sieve. -/
theorem large_sieve_real_interval
    (s : Finset ℕ) (a : ℕ → ℂ) (Q : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ x ≤ n ∧ (n : ℝ) ≤ y) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
      (y - x + 2 + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  let M := ⌊x⌋₊ - 1
  let U := ⌊y⌋₊
  have hMU : M ≤ U := (Nat.sub_le _ _).trans (Nat.floor_mono hxy)
  have hs' : s ⊆ Ioc M (M + (U - M)) := by
    intro n hn
    have hn1 := (hs n hn).1
    have hxn : ⌊x⌋₊ ≤ n := by
      have := (Nat.floor_le hx).trans (hs n hn).2.1
      exact_mod_cast this
    have hny : n ≤ U := Nat.le_floor (hs n hn).2.2
    rw [Finset.mem_Ioc, Nat.add_sub_of_le hMU]
    dsimp [M]
    omega
  have hMlow : x - 2 ≤ (M : ℝ) := by
    have hfloor := Nat.lt_floor_add_one x
    have hnat : ⌊x⌋₊ ≤ M + 1 := by dsimp [M]; omega
    have hnatR : (⌊x⌋₊ : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  have hUL : ((U - M : ℕ) : ℝ) ≤ y - x + 2 := by
    rw [Nat.cast_sub hMU]
    have hu : (U : ℝ) ≤ y := Nat.floor_le (hx.trans hxy)
    linarith
  apply (large_sieve_finset s a M (U - M) Q hs').trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
  linarith


/-- Finite Dirichlet polynomial for Gallagher 1970 p.331 display 11. -/
noncomputable def characterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * χ n * Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)


/-- Primitive character mean square for Gallagher 1970 p.332 display 15. -/
noncomputable def hybridEnergy (Q N : ℕ) (a : ℕ → ℂ) (T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2


/-- The prime detector sum S of Gallagher 1970 p.333. -/
noncomputable def primeDetector {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x y v : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
    (Real.log p / (p : ℝ) : ℂ) * χ p *
      Complex.exp (-((Real.log p * v : ℝ) : ℂ) * Complex.I)


/-- Integrability of the finite frequency window energy. -/
theorem integrable_frequencyWindow_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (δ : ℝ) :
    Integrable (fun x : ℝ => ‖frequencyWindow s a freq δ x‖ ^ 2) := by
  have hi : Integrable (frequencyWindow s a freq δ) := by
    unfold frequencyWindow
    apply integrable_finsetSum
    intro i _
    exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hb (x : ℝ) : ‖frequencyWindow s a freq δ x‖ ≤ ∑ i ∈ s, ‖a i‖ := by
    unfold frequencyWindow
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i _
    by_cases hx : x ∈ Set.Icc (freq i - δ) (freq i)
    · simp [hx]
    · simp [hx]
  apply (hi.norm.const_mul (∑ i ∈ s, ‖a i‖)).mono'
  · exact hi.aestronglyMeasurable.norm.pow 2
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (frequencyWindow s a freq δ x))
    nlinarith


/-- The finite real interval sieve controls every logarithmic window. -/
theorem mellin_window_sieve
    (a : ℕ → ℂ) (Q N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2) ≤
      (Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 N).filter (fun n => u ∈ Set.Icc (Real.log n - δ) (Real.log n))
  have heq {q : ℕ} (χ : DirichletCharacter ℂ q) :
      frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u =
      ∑ n ∈ S, a n * χ n := by
    simp only [frequencyWindow, S, sum_filter, Set.indicator]
  have hnorm : (∑ n ∈ S, ‖a n‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
    simp only [S, sum_filter, Set.indicator]
  have hs : ∀ n ∈ S, 1 ≤ n ∧ Real.exp u ≤ n ∧ (n : ℝ) ≤ Real.exp (u + δ) := by
    intro n hn
    obtain ⟨hnN, hnu⟩ := mem_filter.mp hn
    have hn1 := (mem_Icc.mp hnN).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    refine ⟨hn1, ?_, ?_⟩
    · calc
        Real.exp u ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hnu.2
        _ = _ := Real.exp_log hnpos
    · calc
        (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp (u + δ) := Real.exp_le_exp.mpr (by linarith [hnu.1])
  simpa only [heq, hnorm] using large_sieve_real_interval S a Q
    (Real.exp_pos u).le (Real.exp_le_exp.mpr (by linarith)) hs


/-- The scalar logarithmic window integral in the proof of Gallagher Theorem 3. -/
theorem integral_mellin_window_weight (l B δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ u : ℝ, (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u =
      δ * (B + 2) + (Real.exp δ - 1) * (Real.exp l - Real.exp (l - δ)) := by
  have he : (fun u : ℝ => (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u) =
      (Set.Icc (l - δ) l).indicator (fun u => Real.exp (u + δ) - Real.exp u + 2 + B) := by
    ext u
    by_cases hu : u ∈ Set.Icc (l - δ) l <;> simp [hu]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : l - δ ≤ l)]
  have hd (u : ℝ) : HasDerivAt
      (fun u => (Real.exp δ - 1) * Real.exp u + (B + 2) * u)
      (Real.exp (u + δ) - Real.exp u + 2 + B) u := by
    convert ((Real.hasDerivAt_exp u).const_mul (Real.exp δ - 1)).add
      ((hasDerivAt_id u).const_mul (B + 2)) using 1 <;> first | rfl | (rw [Real.exp_add]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (u + δ) - Real.exp u + 2 + B)).intervalIntegrable _ _)]
  ring


/-- The scalar window coefficient has the hybrid scale, not the pointwise T loss. -/
theorem mellin_window_weight_bound (l B : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ u : ℝ, (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u ≤
      δ * (B + 2) + 2 * δ ^ 2 * Real.exp l := by
  rw [integral_mellin_window_weight l B δ hδ]
  have habs : |δ| ≤ 1 := by rw [abs_of_nonneg hδ]; exact hδ1
  have h₁ : Real.exp δ - 1 ≤ 2 * δ := by
    have := Real.abs_exp_sub_one_le habs
    rw [abs_of_nonneg hδ] at this
    exact (le_abs_self _).trans this
  have h₂ : 1 - Real.exp (-δ) ≤ δ := by linarith [Real.add_one_le_exp (-δ)]
  have h₂0 : 0 ≤ 1 - Real.exp (-δ) := by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hδ)
    linarith
  have hp := mul_le_mul h₁ h₂ h₂0 (by positivity : (0 : ℝ) ≤ 2 * δ)
  have he : Real.exp l - Real.exp (l - δ) = Real.exp l * (1 - Real.exp (-δ)) := by
    rw [Real.exp_sub, Real.exp_neg]
    ring
  rw [he]
  have hpe := mul_le_mul_of_nonneg_right hp (Real.exp_pos l).le
  nlinarith


/-- Integrating the logarithmic windows gives Q squared delta plus n delta squared. -/
theorem integrated_mellin_window_sieve
    (a : ℕ → ℂ) (Q N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ q ∈ Finset.Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
          (fun n => Real.log n) δ u‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 := by
  classical
  let K : ℝ → ℝ := fun u => Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2
  let W {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) :=
    ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
  have hiW {q : ℕ} (χ : DirichletCharacter ℂ q) : Integrable (W χ) :=
    integrable_frequencyWindow_energy _ _ _ _
  have hiR (n : ℕ) : Integrable (fun u => K u *
      (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u) := by
    have heq : (fun u => K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator
        (fun _ => ‖a n‖ ^ 2) u) =
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun u => K u * ‖a n‖ ^ 2) := by
      ext u
      by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n) <;> simp [hu]
    rw [heq]
    exact (by dsimp [K]; fun_prop : Continuous (fun u => K u * ‖a n‖ ^ 2)).integrableOn_Icc.integrable_indicator measurableSet_Icc
  have heq (q : ℕ) :
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) =
      ∫ u, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ u :=
    (integral_finsetSum _ (fun χ _ => hiW χ)).symm
  change (∑ q ∈ Finset.Icc 1 Q,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) ≤ _
  simp_rw [heq]
  rw [← integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun χ _ => hiW χ))]
  calc
    _ ≤ ∫ u, ∑ n ∈ Finset.Icc 1 N, K u *
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
      apply integral_mono
        (integrable_finsetSum _ (fun q _ => integrable_finsetSum _ (fun χ _ => hiW χ)))
        (integrable_finsetSum _ (fun n _ => hiR n))
      intro u
      dsimp only [W, K]
      rw [← mul_sum]
      exact mellin_window_sieve a Q N hδ.le u
    _ = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 *
        ∫ u : ℝ, K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => (1 : ℝ)) u := by
      rw [integral_finsetSum _ (fun n _ => hiR n)]
      apply sum_congr rfl
      intro n _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n)
      · simp [hu]; ring
      · simp [hu]
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hb := mellin_window_weight_bound (Real.log n) ((Q : ℝ) ^ 2) hδ.le hδ1
      rw [Real.exp_log hnpos] at hb
      dsimp [K]
      have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖a n‖)
      nlinarith


/-- Rescaling the Dirichlet polynomial height by two pi. -/
theorem characterPolynomial_time_integral {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) =
      (2 * Real.pi) * ∫ t in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
        ‖∑ n ∈ Finset.Icc 1 N, (a n * χ n) * LeanLab.PNTPort.LargeSieve.e (Real.log n * t)‖ ^ 2 := by
  let c : ℝ := -1 / (2 * Real.pi)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  let P : ℝ → ℝ := fun t => ‖∑ n ∈ Finset.Icc 1 N, (a n * χ n) * LeanLab.PNTPort.LargeSieve.e (Real.log n * t)‖ ^ 2
  have heq (v : ℝ) : ‖characterPolynomial χ a N v‖ ^ 2 = P (c * v) := by
    congr 2
    unfold characterPolynomial
    apply sum_congr rfl
    intro n _
    congr 1
    unfold LeanLab.PNTPort.LargeSieve.e
    congr 1
    dsimp [c]
    push_cast
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_comp_mul_left P hc]
  have h₁ : c * (-T) = T / (2 * Real.pi) := by dsimp [c]; ring
  have h₂ : c * T = -(T / (2 * Real.pi)) := by dsimp [c]; ring
  rw [h₁, h₂, intervalIntegral.integral_symm]
  dsimp [c, P]
  simp only [inv_div, inv_neg, inv_one, smul_eq_mul]
  ring


/-- Gallagher Theorem 3 from the sharp finite multiplicative large sieve. -/
theorem hybrid_mean_value_bound
    (Q N : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    hybridEnergy Q N a T ≤ (2 * Real.pi ^ 3) *
      ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  classical
  let δ : ℝ := 1 / T
  have hTpos : 0 < T := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_one hTpos]; exact hT
  let C : ℝ := Real.pi ^ 3 / (2 * δ ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let W {q : ℕ} (χ : DirichletCharacter ℂ q) :=
    ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
  have htime {q : ℕ} (χ : DirichletCharacter ℂ q) :
      (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) ≤ C * W χ := by
    rw [characterPolynomial_time_integral]
    have hnear : δ * (T / (2 * Real.pi)) ≤ 1 / 2 := by
      dsimp [δ]
      have he : (1 / T) * (T / (2 * Real.pi)) = 1 / (2 * Real.pi) := by field_simp
      rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Real.pi_gt_three]
    have hh := gallagher_window_smoothing (Finset.Icc 1 N) (fun n => a n * χ n)
      (fun n => Real.log n) hδ (div_nonneg hTpos.le (by positivity)) hnear
    apply (mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).trans_eq
    dsimp [C, W]
    ring
  unfold hybridEnergy
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), C * W χ :=
      sum_le_sum (fun q _ => sum_le_sum (fun χ _ => htime χ))
    _ = C * (∑ q ∈ Finset.Icc 1 Q,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ) := by
      simp only [mul_sum]
    _ ≤ C * ∑ n ∈ Finset.Icc 1 N, (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (integrated_mellin_window_sieve a Q N hδ hδ1) hC
    _ ≤ _ := by
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro n _
      rw [← mul_assoc, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hQsq : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
      have he : C * (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) =
          (Real.pi ^ 3 / 2) * T * ((Q : ℝ) ^ 2 + 2) + Real.pi ^ 3 * n := by
        dsimp [C, δ]
        field_simp
      rw [he]
      have hmult := mul_le_mul_of_nonneg_left
        (show (Q : ℝ) ^ 2 + 2 ≤ 3 * (Q : ℝ) ^ 2 by linarith)
        (show 0 ≤ (Real.pi ^ 3 / 2) * T by positivity)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hrest : 0 ≤ Real.pi ^ 3 * ((Q : ℝ) ^ 2 * T) := by positivity
      have hrest2 : 0 ≤ Real.pi ^ 3 * n := by positivity
      nlinarith


/-- Continuity in the height variable does not require an analytic number theory input. -/
theorem continuous_characterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) : Continuous (characterPolynomial χ a N) := by
  unfold characterPolynomial
  fun_prop


/-- Nonnegativity of the hybrid energy for nonnegative time. -/
theorem hybridEnergy_nonneg (Q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ hybridEnergy Q N a T := by
  unfold hybridEnergy
  apply sum_nonneg
  intro q _
  apply sum_nonneg
  intro χ _
  exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)


/-- Unit modulus of the height twist. -/
theorem norm_mellin_twist (n : ℕ) (t : ℝ) :
    ‖Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, neg_zero, mul_zero, zero_mul, sub_zero, Real.exp_zero]


/-- Integrating a fixed pointwise family bound gives the length of the time interval. -/
theorem hybridEnergy_le_of_pointwise (Q N : ℕ) (a : ℕ → ℂ) {T B : ℝ}
    (hT : 0 ≤ T)
    (hbound : ∀ t : ℝ, -T ≤ t → t ≤ T →
      ∑ q ∈ Icc 1 Q,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖characterPolynomial χ a N t‖ ^ 2 ≤ B) :
    hybridEnergy Q N a T ≤ 2 * T * B := by
  classical
  have hc {q : ℕ} (χ : DirichletCharacter ℂ q) :
      Continuous (fun t => ‖characterPolynomial χ a N t‖ ^ 2) :=
    (continuous_characterPolynomial χ a N).norm.pow 2
  have heq (q : ℕ) :
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) =
      ∫ t in (-T)..T,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖characterPolynomial χ a N t‖ ^ 2 :=
    (intervalIntegral.integral_finsetSum (fun χ _ => (hc χ).intervalIntegrable _ _)).symm
  unfold hybridEnergy
  simp_rw [heq]
  rw [← intervalIntegral.integral_finsetSum (fun q _ =>
    (continuous_finsetSum _ (fun χ _ => hc χ)).intervalIntegrable _ _)]
  calc
    _ ≤ ∫ t in (-T)..T, B := intervalIntegral.integral_mono_on (by linarith)
      ((continuous_finsetSum _ (fun q _ =>
        continuous_finsetSum _ (fun χ _ => hc χ))).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun t ht => hbound t ht.1 ht.2)
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring


/-- Pointwise application of the already proved multiplicative large sieve. -/
theorem characterPolynomial_pointwise_sieve
    (Q N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ q ∈ Icc 1 Q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖characterPolynomial χ a N t‖ ^ 2) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  let b : ℕ → ℂ := fun n => a n * Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)
  have hI : Ioc 0 (0 + N) = Icc 1 N := by ext n; simp; omega
  have heq {q : ℕ} (χ : DirichletCharacter ℂ q) :
      characterPolynomial χ a N t = ∑ n ∈ Ioc 0 (0 + N), b n * χ n := by
    rw [hI]
    unfold characterPolynomial
    apply sum_congr rfl
    intro n _
    dsimp [b]
    ring
  have hnorm (n : ℕ) : ‖b n‖ = ‖a n‖ := by
    dsimp [b]
    rw [norm_mul, norm_mellin_twist, mul_one]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖characterPolynomial χ a N t‖ ^ 2 := by
      apply sum_le_sum
      intro q hq
      have hq0 : 0 < q := (mem_Icc.mp hq).1
      have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
      have hweight : (1 : ℝ) ≤ q / (q.totient : ℝ) := (le_div_iff₀ hφ0).mpr (by simpa using hφq)
      exact le_mul_of_one_le_left (sum_nonneg (fun _ _ => sq_nonneg _)) hweight
    _ = _ := by simp_rw [heq]
    _ ≤ _ := large_sieve b 0 N Q
    _ = _ := by rw [hI]; simp_rw [hnorm]


/-- Direct time integration of the pointwise sieve, with its full T loss visible. -/
theorem hybridEnergy_pointwise_bound
    (Q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    hybridEnergy Q N a T ≤
      2 * T * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
  have hh := hybridEnergy_le_of_pointwise Q N a hT
    (fun t _ _ => characterPolynomial_pointwise_sieve Q N a t)
  exact hh.trans_eq (by ring)


/-- The full hybrid coefficient follows for support length at most Q squared. -/
theorem hybridEnergy_short_support
    (Q N : ℕ) (a : ℕ → ℂ) (hN : N ≤ Q ^ 2) {T : ℝ} (hT : 0 ≤ T) :
    hybridEnergy Q N a T ≤
      4 * ∑ n ∈ Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  have hNr : (N : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hN
  calc
    _ ≤ 2 * T * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 :=
      hybridEnergy_pointwise_bound Q N a hT
    _ ≤ (4 * ((Q : ℝ) ^ 2 * T)) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
      nlinarith
    _ = 4 * ∑ n ∈ Icc 1 N, ((Q : ℝ) ^ 2 * T) * ‖a n‖ ^ 2 := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro n _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact le_add_of_nonneg_right (Nat.cast_nonneg n)


/-- The pointwise sieve coefficient does not imply the hybrid coefficient uniformly. -/
theorem pointwise_hybrid_coefficient_insufficient (C : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ C * ((N : ℝ) + N) < 2 * N * ((N : ℝ) + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 1)
  have hN1 : (1 : ℝ) < N := (le_max_right _ _).trans_lt hN
  have hNC : C < (N : ℝ) := (le_max_left _ _).trans_lt hN
  refine ⟨N, by exact_mod_cast hN1.le, ?_⟩
  nlinarith


/-- Weighted Schwarz step in Gallagher 1970 p.336 before display 25. -/
theorem detector_weighted_cauchy {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (f w : α → ℝ) (hw : ∀ᵐ x ∂measure, 0 ≤ w x)
    (hwi : Integrable w measure) (hfi : Integrable (fun x => f x * w x) measure)
    (hf2i : Integrable (fun x => f x ^ 2 * w x) measure)
    (hwpos : 0 < ∫ x, w x ∂measure) :
    (∫ x, f x * w x ∂measure) ^ 2 ≤ (∫ x, w x ∂measure) * ∫ x, f x ^ 2 * w x ∂measure := by
  let c : ℝ := (∫ x, f x * w x ∂measure) / (∫ x, w x ∂measure)
  have heq : (fun x => (f x - c) ^ 2 * w x) =
      fun x => f x ^ 2 * w x - (2 * c) * (f x * w x) + c ^ 2 * w x := by
    ext x
    ring
  have _hi : Integrable (fun x => (f x - c) ^ 2 * w x) measure := by
    rw [heq]
    exact (hf2i.sub (hfi.const_mul _)).add (hwi.const_mul _)
  have hp : 0 ≤ ∫ x, (f x - c) ^ 2 * w x ∂measure :=
    integral_nonneg_of_ae (hw.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
  rw [heq] at hp
  rw [integral_add (f := fun x => f x ^ 2 * w x - (2 * c) * (f x * w x))
    (g := fun x => c ^ 2 * w x) (hf2i.sub (hfi.const_mul _)) (hwi.const_mul _),
    integral_sub (f := fun x => f x ^ 2 * w x)
    (g := fun x => (2 * c) * (f x * w x)) hf2i (hfi.const_mul _),
    integral_const_mul, integral_const_mul] at hp
  have hc : c * (∫ x, w x ∂measure) = ∫ x, f x * w x ∂measure := by
    dsimp [c]
    exact div_mul_cancel₀ _ hwpos.ne'
  nlinarith [mul_nonneg hp hwpos.le]


/-- Squaring a supplied L1 detector gives its weighted L2 lower bound. -/
theorem detector_l2_of_l1 {α : Type*} [MeasurableSpace α] (measure : Measure α)
    (f w : α → ℝ) (hw : ∀ᵐ x ∂measure, 0 ≤ w x)
    (hwi : Integrable w measure) (hfi : Integrable (fun x => f x * w x) measure)
    (hf2i : Integrable (fun x => f x ^ 2 * w x) measure)
    (hwpos : 0 < ∫ x, w x ∂measure) {H : ℝ} (hH : 0 ≤ H)
    (hlower : H ≤ ∫ x, f x * w x ∂measure) :
    H ^ 2 / (∫ x, w x ∂measure) ≤ ∫ x, f x ^ 2 * w x ∂measure := by
  have hc := detector_weighted_cauchy measure f w hw hwi hfi hf2i hwpos
  rw [div_le_iff₀ hwpos]
  nlinarith


/-- Logarithmic mass in the Schwarz step before Gallagher 1970 display 25. -/
theorem logarithmic_window_mass {x : ℝ} (hx : 0 < x) (B : ℝ) :
    ∫ y in x..(x ^ B), (1 : ℝ) / y = (B - 1) * Real.log x := by
  rw [integral_one_div_of_pos hx (Real.rpow_pos_of_pos hx B),
    Real.log_div (Real.rpow_pos_of_pos hx B).ne' hx.ne', Real.log_rpow hx]
  ring


/-- Prime coefficient estimate in Gallagher 1970 p.336 after display 25. -/
theorem prime_log_sq_div_sum_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p ≤ Real.log N * (Real.log N + 7) := by
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, Real.log N * (Real.log p / p) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hlog : Real.log p ≤ Real.log N :=
        Real.log_le_log hp0 (by exact_mod_cast hpN)
      have hlog0 : 0 ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
      have h := mul_le_mul_of_nonneg_right hlog (div_nonneg hlog0 hp0.le)
      convert h using 1; ring
    _ = Real.log N * LeanLab.PNTSieve.Mertens.C N := by
      rw [LeanLab.PNTSieve.Mertens.C_eq, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (LeanLab.PNTSieve.Mertens.C_le N hN) hL


/-- Large prime support removes the Q squared T part of the hybrid coefficient. -/
theorem prime_detector_coefficient_energy_le (N : ℕ) (hN : 1 ≤ N)
    (s : Finset ℕ) {K : ℝ}
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ N ∧ K ≤ p) :
    ∑ p ∈ s, (K + p) * (Real.log p / p) ^ 2 ≤
      2 * Real.log N * (Real.log N + 7) := by
  have hsub : s ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(hs p hp).2.1, (hs p hp).1⟩
  calc
    _ ≤ ∑ p ∈ s, 2 * (Real.log p ^ 2 / p) := by
      apply sum_le_sum
      intro p hp
      have hpp := hs p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.1.pos
      have hmul := mul_le_mul_of_nonneg_right hpp.2.2 (sq_nonneg (Real.log p / p))
      calc
        (K + p) * (Real.log p / p) ^ 2 ≤ ((p : ℝ) + p) * (Real.log p / p) ^ 2 := by
          nlinarith
        _ = 2 * (Real.log p ^ 2 / p) := by field_simp; ring
    _ ≤ ∑ p ∈ Nat.primesLE N, 2 * (Real.log p ^ 2 / p) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = 2 * ∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p := (mul_sum ..).symm
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left (prime_log_sq_div_sum_le N hN) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith


/-- Gallagher 1970 p.332 Theorem 3 display 15, derived here from
Theorem 1 and Lemma 3. The finite Dirichlet polynomial starts at one.
There is no unrestricted additive shift in the coefficient on the right. -/
theorem gallagher_hybrid_mean_value : ∃ C : ℝ, 0 < C ∧
    ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T → ∀ N : ℕ, ∀ a : ℕ → ℂ,
      hybridEnergy Q N a T ≤
        C * ∑ n ∈ Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  refine ⟨2 * Real.pi ^ 3, by positivity, ?_⟩
  intro Q hQ T hT N a
  exact hybrid_mean_value_bound Q N hQ a hT


/-- LEAF. Gallagher 1970 pp.333 to 335, Theorem 5 display 20.
CONDITIONAL ON the finite Turan power bound. The remaining proof is the analytic
logarithmic derivative expansion, its tail estimate, prime power removal and partial summation.
The principal character height exclusion is part of the source statement. -/
theorem gallagher_zero_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  sorry


/-- Gallagher 1970 p.333 Theorem 5 display 20.
CONDITIONAL ON turan_interpolant and gallagher_zero_detector_of_turan. -/
theorem gallagher_zero_detector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  exact gallagher_zero_detector_of_turan
    (fun n M hn hnM z hz => turan_power_sum_lower_bound hn hnM z hz)


/-- Complex coefficient form of the finite Gauss identity in Gallagher 1970 p.333.
The conjugated additive coefficients account for the conjugate character in the Gauss sum.
This identity is one finite input to display 18. -/
theorem weighted_gauss_parseval {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ)
    (hs : ∀ n ∈ s, IsUnit (n : ZMod q)) :
    (q.totient : ℝ) * ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit,
      ‖∑ n ∈ s, star (a n) * stdAddChar (b * (n : ZMod q))‖ ^ 2 =
    ∑ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
  rw [← LeanLab.RieselVaughan1983.GaussImprim.sum_norm_sq_twist]
  apply sum_congr rfl
  intro χ _
  have he : ∑ b, χ b * ∑ n ∈ s, star (a n) * stdAddChar (b * (n : ZMod q)) =
      gaussSum χ stdAddChar * star (∑ n ∈ s, a n * χ (n : ZMod q)) := by
    calc
      _ = ∑ n ∈ s, star (a n) * ∑ b, χ b * stdAddChar (b * (n : ZMod q)) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro b _
        ring
      _ = ∑ n ∈ s, star (a n) * (gaussSum χ stdAddChar * star (χ (n : ZMod q))) := by
        apply sum_congr rfl
        intro n hn
        congr 1
        have hu := hs n hn
        have h := gaussSum_mulShift_eq χ stdAddChar hu.unit
        rw [hu.unit_spec, gaussSum] at h
        rw [MulChar.star_apply', mul_comm (gaussSum χ stdAddChar), ← h]
        apply sum_congr rfl
        intro b _
        rw [AddChar.mulShift_apply, mul_comm (n : ZMod q) b]
      _ = _ := by
        rw [star_sum, mul_sum]
        apply sum_congr rfl
        intro n _
        rw [star_mul]
        ring
  rw [he, norm_mul, mul_pow, norm_star]


/-- Complex coefficient conductor regrouping in Gallagher 1970 p.333 display 19.
The support is prime to the larger modulus so changing level preserves every term. -/
theorem weighted_character_conductor_fiber (s : Finset ℕ) (a : ℕ → ℂ)
    {q r : ℕ} [NeZero q] (hrq : r ∣ q) (hs : ∀ n ∈ s, n.Coprime q) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = r),
      ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2) =
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
      ‖∑ n ∈ s, a n * ψ (n : ZMod r)‖ ^ 2 := by
  classical
  have hr : r ≠ 0 := by
    rintro rfl
    exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hrq)
  letI : NeZero r := ⟨hr⟩
  symm
  apply sum_bij (fun ψ _ => DirichletCharacter.changeLevel hrq ψ)
  · intro ψ hψ
    rw [mem_filter] at hψ ⊢
    exact ⟨mem_univ _, by rw [DirichletCharacter.conductor_changeLevel]; exact hψ.2⟩
  · intro ψ1 _ ψ2 _ h
    exact DirichletCharacter.changeLevel_injective hrq h
  · intro χ hχ
    rw [mem_filter] at hχ
    have hf : χ.FactorsThrough r := by
      have := χ.factorsThrough_conductor
      rwa [hχ.2] at this
    obtain ⟨_, χ₀, hχ₀⟩ := hf
    refine ⟨χ₀, ?_, hχ₀.symm⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← DirichletCharacter.conductor_changeLevel χ₀ hrq, ← hχ₀, hχ.2]
  · intro ψ _
    congr 2
    apply sum_congr rfl
    intro n hn
    congr 1
    have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr (hs n hn)
    have he := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hrq hu.unit
    rw [hu.unit_spec] at he
    rw [he, ZMod.cast_natCast hrq]

/-- Finite conductor lower bound in Gallagher 1970 p.333 display 19.
Only squarefree conductor multiples prime to the conductor are retained. -/
theorem weighted_gauss_conductor_lower (s : Finset ℕ) (a : ℕ → ℂ)
    {q : ℕ} [NeZero q] (hs : ∀ n ∈ s, n.Coprime q) :
    (∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
      ((μ (q / r) : ℤ) : ℝ) ^ 2 * r *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
          ‖∑ n ∈ s, a n * ψ (n : ZMod r)‖ ^ 2) ≤
    ∑ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
  classical
  have hq : q ≠ 0 := NeZero.ne q
  let E : ℕ → ℝ := fun r =>
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.conductor = r),
      ‖∑ n ∈ s, a n * ψ (n : ZMod r)‖ ^ 2
  change (∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
    ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r) ≤ _
  set good : DirichletCharacter ℂ q → Prop :=
    fun χ => Squarefree (q / χ.conductor) ∧ χ.conductor.Coprime (q / χ.conductor)
  calc ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r
      = ∑ r ∈ q.divisors.filter (fun r => Squarefree (q / r) ∧ r.Coprime (q / r)),
          ∑ χ ∈ (univ.filter good).filter (fun χ => χ.conductor = r),
            ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
        rw [sum_filter, sum_filter]
        refine sum_congr rfl fun r hr => ?_
        have hrq : r ∣ q := Nat.dvd_of_mem_divisors hr
        by_cases hsq : Squarefree (q / r)
        · by_cases hc : r.Coprime (q / r)
          · rw [if_pos hc.symm, if_pos ⟨hsq, hc⟩, filter_filter]
            have hf : univ.filter (fun χ : DirichletCharacter ℂ q => good χ ∧ χ.conductor = r) =
                univ.filter (fun χ => χ.conductor = r) := by
              ext χ; simp only [mem_filter, mem_univ, true_and, good]
              constructor
              · exact fun h => h.2
              · intro h; refine ⟨?_, h⟩; rw [h]; exact ⟨hsq, hc⟩
            rw [hf]
            dsimp only [E]
            rw [← weighted_character_conductor_fiber s a hrq hs, mul_sum]
            refine sum_congr rfl fun χ hχ => ?_
            rw [mem_filter] at hχ
            have hg : good χ := by simp only [good]; rw [hχ.2]; exact ⟨hsq, hc⟩
            have hm : ((μ (q / r) : ℤ) : ℝ) ^ 2 = 1 := by
              exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
            rw [LeanLab.RieselVaughan1983.GaussImprim.norm_sq_gaussSum_eq_conductor χ hg.1 hg.2, hχ.2, hm]
            ring
          · rw [if_neg (fun h => hc h.symm), if_neg (fun h => hc h.2)]
        · have hm0 : ((μ (q / r) : ℤ) : ℝ) = 0 := by
            rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
          simp [hsq]
      _ = ∑ χ ∈ univ.filter good,
            ‖gaussSum χ stdAddChar‖ ^ 2 * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 := by
        refine sum_fiberwise_of_maps_to
          (g := fun χ : DirichletCharacter ℂ q => χ.conductor) (fun χ hχ => ?_) _
        rw [mem_filter] at hχ ⊢
        exact ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq⟩, hχ.2⟩
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The logarithmic conductor gain in Gallagher 1970 p.333 after display 19.
The proof uses the coprime Moebius over totient lower bound already proved in the lab. -/
theorem logarithmic_conductor_weight_le
    (Q : ℕ) (E : ℕ → ℝ) (hE : ∀ r ∈ Finset.Icc 1 Q, 0 ≤ E r) :
    (∑ r ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / r) * E r) ≤
    ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ *
      ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r := by
  let F : ℕ → ℕ → ℝ := fun r m => ((μ m : ℤ) : ℝ) ^ 2 * r / ((r * m).totient : ℝ) * E r
  have heq : (∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ *
      ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r), F r (q / r) := by
    apply sum_congr rfl
    intro q _
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    have hrd : r ∣ q := Nat.dvd_of_mem_divisors (mem_filter.mp hr).1
    dsimp [F]
    rw [Nat.mul_div_cancel' hrd]
    ring
  rw [heq, LeanLab.RieselVaughan1983.Page65.sum_swap]
  apply sum_le_sum
  intro r hr
  have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hlog := mul_le_mul_of_nonneg_right
    (LeanLab.RieselVaughan1983.MuPhi.log_le_mu_phi_sum r hr1 ((Q : ℝ) / r) (div_nonneg (Nat.cast_nonneg _) hrpos.le)) (hE r hr)
  apply hlog.trans_eq
  have hset := LeanLab.RieselVaughan1983.Page65.m_range hr1 (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)
  simp only [Nat.floor_natCast] at hset
  rw [hset, mul_sum, sum_mul]
  apply sum_congr rfl
  intro m hm
  simp only [mem_filter, mem_Icc] at hm
  have hφr : (r.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  have hφm : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  dsimp [F]
  rw [Nat.totient_mul hm.2.2.symm]
  push_cast
  field_simp

/-- The finite rough support character sieve reduces to the sharp additive sieve.
Gallagher 1970 pp.332 and 333, displays 17 through 19. -/
theorem rough_character_sieve_le_additive
    (s : Finset ℕ) (a : ℕ → ℂ) (Q : ℕ)
    (hs : ∀ n ∈ s, ∀ q ∈ Finset.Icc 1 Q, n.Coprime q) :
    (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
    ∑ q ∈ Finset.Icc 1 Q, ∑ c ∈ (range q).filter (fun c => c.Coprime q),
      ‖∑ n ∈ s, star (a n) * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 := by
  classical
  let E : ℕ → ℝ := fun q =>
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q),
      ‖∑ n ∈ s, a n * χ n‖ ^ 2
  have hEeq (q : ℕ) : E q =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2 := by
    dsimp only [E]
    rw [sum_filter, sum_filter]
    apply sum_congr rfl
    intro χ _
    by_cases hχ : χ.conductor = q
    · simp [DirichletCharacter.IsPrimitive, hχ]
    · simp [DirichletCharacter.IsPrimitive, hχ]
  simp_rw [← hEeq]
  apply (logarithmic_conductor_weight_le Q E (fun q _ => sum_nonneg (fun χ _ => sq_nonneg _))).trans
  apply sum_le_sum
  intro q hq
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  letI : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlow := weighted_gauss_conductor_lower s a (fun n hn => hs n hn q hq)
  have hunit : ∀ n ∈ s, IsUnit (n : ZMod q) :=
    fun n hn => (ZMod.isUnit_iff_coprime n q).mpr (hs n hn q hq)
  rw [← weighted_gauss_parseval s a hunit] at hlow
  have hdiv : (q.totient : ℝ)⁻¹ *
      (∑ r ∈ q.divisors.filter (fun r => (q / r).Coprime r),
        ((μ (q / r) : ℤ) : ℝ) ^ 2 * r * E r) ≤
      ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit,
        ‖∑ n ∈ s, star (a n) * stdAddChar (b * (n : ZMod q))‖ ^ 2 := by
    rw [inv_mul_le_iff₀ hφ]
    exact hlow
  apply hdiv.trans_eq
  rw [sum_filter, LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, sum_filter]
  apply sum_congr rfl
  intro c _
  by_cases hc : c.Coprime q
  · rw [if_pos ((ZMod.isUnit_iff_coprime c q).mpr hc), if_pos hc]
    congr 2
    apply sum_congr rfl
    intro n _
    congr 1
    rw [mul_comm (c : ZMod q) (n : ZMod q)]
    simpa only [Int.cast_natCast] using
      LeanLab.PNTPort.LargeSieve.stdAddChar_mul_natCast (q := q) (n : ℤ) c
  · rw [if_neg (fun h => hc ((ZMod.isUnit_iff_coprime c q).mp h)), if_neg hc]

/-- Gallagher 1970 p.332 Lemma 4 display 17, proved using the complex coefficient
Gauss identity, conductor regrouping and the coprime Moebius over totient lower bound
on p.333 displays 18 and 19. For integer endpoints the constant can be one. -/
theorem gallagher_rough_finite_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ (a : ℕ → ℂ) (M L : ℕ),
      (∀ n ∈ Finset.Ioc M (M + L), ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), a n * χ n‖ ^ 2) ≤
        C * ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + L), ‖a n‖ ^ 2 := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro Q hQ a M L hrough
  let S : Finset ℕ := (Finset.Ioc M (M + L)).filter (fun n => a n ≠ 0)
  have hs : ∀ n ∈ S, ∀ q ∈ Finset.Icc 1 Q, n.Coprime q := by
    intro n hn q hq
    obtain ⟨hnI, hna⟩ := mem_filter.mp hn
    by_contra hc
    obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpQ : p ≤ Q := (Nat.le_of_dvd (by have := (mem_Icc.mp hq).1; omega) hpq).trans (mem_Icc.mp hq).2
    exact hna (hrough n hnI p hp hpQ hpn)
  have hsum (f : ℕ → ℂ) : (∑ n ∈ S, a n * f n) = ∑ n ∈ Finset.Ioc M (M + L), a n * f n := by
    dsimp [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : a n = 0 <;> simp [hn]
  have hstar (f : ℕ → ℂ) : (∑ n ∈ S, star (a n) * f n) =
      ∑ n ∈ Finset.Ioc M (M + L), star (a n) * f n := by
    dsimp [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : a n = 0 <;> simp [hn]
  have hb := rough_character_sieve_le_additive S a Q hs
  simp_rw [hsum, hstar] at hb
  apply hb.trans
  simpa only [norm_star, one_mul] using additive_large_sieve_sharp (fun n => star (a n)) M L Q

/-- Gallagher 1970 p.332 Theorem 4 from its finite Lemma 4 input.
CONDITIONAL ON the supplied finite rough support sieve. The time smoothing is proved here. -/
theorem hybrid_of_weighted_finite_sieve
    (Q : ℕ) (hQ : 1 ≤ Q) (C : ℝ) (hC : 0 ≤ C) (weight : ℕ → ℝ)
    (hw : ∀ q ∈ Finset.Icc 1 Q, 0 ≤ weight q)
    (hfinite : ∀ (b : ℕ → ℂ) (M L : ℕ),
      (∀ n ∈ Finset.Ioc M (M + L), ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → b n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), b n * χ n‖ ^ 2) ≤
        C * ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + L), ‖b n‖ ^ 2)
    (N : ℕ) (a : ℕ → ℂ)
    (hrough : ∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0)
    {T : ℝ} (hT : 1 ≤ T) :
    (∑ q ∈ Finset.Icc 1 Q, weight q *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
      (2 * Real.pi ^ 3 * C) *
        ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  have hsieve (s : Finset ℕ) (M L : ℕ) (hs : s ⊆ Finset.Ioc M (M + L))
      (hsN : s ⊆ Finset.Icc 1 N) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
        C * ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
    let b : ℕ → ℂ := fun n => if n ∈ s then a n else 0
    have hb : ∀ n ∈ Finset.Ioc M (M + L), ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → b n = 0 := by
      intro n _ p hp hpQ hpn
      by_cases hn : n ∈ s
      · simp only [b, if_pos hn]
        exact hrough n (hsN hn) p hp hpQ hpn
      · simp [b, hn]
    have hset : (Finset.Ioc M (M + L)).filter (fun n => n ∈ s) = s := by
      ext n
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hn => hs hn)
    have hsum {q : ℕ} (χ : DirichletCharacter ℂ q) :
        (∑ n ∈ Finset.Ioc M (M + L), b n * χ n) = ∑ n ∈ s, a n * χ n := by
      simp only [b, ite_mul, zero_mul, ← sum_filter, hset]
    have henergy : (∑ n ∈ Finset.Ioc M (M + L), ‖b n‖ ^ 2) = ∑ n ∈ s, ‖a n‖ ^ 2 := by
      simp only [b, apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
        ← sum_filter, hset]
    simpa only [hsum, henergy] using hfinite b M L hb
  have hreal (s : Finset ℕ) (hsN : s ⊆ Finset.Icc 1 N) {x y : ℝ}
      (hx : 0 ≤ x) (hxy : x ≤ y)
      (hs : ∀ n ∈ s, 1 ≤ n ∧ x ≤ n ∧ (n : ℝ) ≤ y) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ s, a n * χ n‖ ^ 2) ≤
        C * (y - x + 2 + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
    let M := ⌊x⌋₊ - 1
    let U := ⌊y⌋₊
    have hMU : M ≤ U := (Nat.sub_le _ _).trans (Nat.floor_mono hxy)
    have hs' : s ⊆ Finset.Ioc M (M + (U - M)) := by
      intro n hn
      have hn1 := (hs n hn).1
      have hxn : ⌊x⌋₊ ≤ n := by
        have := (Nat.floor_le hx).trans (hs n hn).2.1
        exact_mod_cast this
      have hny : n ≤ U := Nat.le_floor (hs n hn).2.2
      rw [Finset.mem_Ioc, Nat.add_sub_of_le hMU]
      dsimp [M]
      omega
    have hMlow : x - 2 ≤ (M : ℝ) := by
      have hfloor := Nat.lt_floor_add_one x
      have hnat : ⌊x⌋₊ ≤ M + 1 := by dsimp [M]; omega
      have hnatR : (⌊x⌋₊ : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hnat
      linarith
    have hUL : ((U - M : ℕ) : ℝ) ≤ y - x + 2 := by
      rw [Nat.cast_sub hMU]
      have hu : (U : ℝ) ≤ y := Nat.floor_le (hx.trans hxy)
      linarith
    apply (hsieve s M (U - M) hs' hsN).trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _ => sq_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hwindow {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2) ≤
        C * (Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
    let S : Finset ℕ := (Finset.Icc 1 N).filter (fun n => u ∈ Set.Icc (Real.log n - δ) (Real.log n))
    have heq {q : ℕ} (χ : DirichletCharacter ℂ q) :
        frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u =
        ∑ n ∈ S, a n * χ n := by
      simp only [frequencyWindow, S, sum_filter, Set.indicator]
    have hnorm : (∑ n ∈ S, ‖a n‖ ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
      simp only [S, sum_filter, Set.indicator]
    have hs : ∀ n ∈ S, 1 ≤ n ∧ Real.exp u ≤ n ∧ (n : ℝ) ≤ Real.exp (u + δ) := by
      intro n hn
      obtain ⟨hnN, hnu⟩ := mem_filter.mp hn
      have hn1 := (mem_Icc.mp hnN).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      refine ⟨hn1, ?_, ?_⟩
      · calc
          Real.exp u ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hnu.2
          _ = _ := Real.exp_log hnpos
      · calc
          (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
          _ ≤ Real.exp (u + δ) := Real.exp_le_exp.mpr (by linarith [hnu.1])
    simpa only [heq, hnorm] using hreal S (filter_subset _ _) (Real.exp_pos u).le
      (Real.exp_le_exp.mpr (by linarith)) hs
  have hintegrated {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
      (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
            (fun n => Real.log n) δ u‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 := by
    let K : ℝ → ℝ := fun u => Real.exp (u + δ) - Real.exp u + 2 + (Q : ℝ) ^ 2
    let W {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) :=
      ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
    have hiW {q : ℕ} (χ : DirichletCharacter ℂ q) : Integrable (W χ) :=
      integrable_frequencyWindow_energy _ _ _ _
    have hiR (n : ℕ) : Integrable (fun u => K u *
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u) := by
      have heq : (fun u => K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator
          (fun _ => ‖a n‖ ^ 2) u) =
          (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun u => K u * ‖a n‖ ^ 2) := by
        ext u
        by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n) <;> simp [hu]
      rw [heq]
      exact (by dsimp [K]; fun_prop : Continuous (fun u => K u * ‖a n‖ ^ 2)).integrableOn_Icc.integrable_indicator measurableSet_Icc
    have heq (q : ℕ) :
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) =
        ∫ u, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ u :=
      (integral_finsetSum _ (fun χ _ => hiW χ)).symm
    change (∑ q ∈ Finset.Icc 1 Q, weight q *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), ∫ u, W χ u) ≤ _
    simp_rw [heq, ← integral_const_mul]
    rw [← integral_finsetSum _ (fun q _ => (integrable_finsetSum _ (fun χ _ => hiW χ)).const_mul _)]
    calc
      _ ≤ ∫ u, C * ∑ n ∈ Finset.Icc 1 N, K u *
          (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
        apply integral_mono
          (integrable_finsetSum _ (fun q _ => (integrable_finsetSum _ (fun χ _ => hiW χ)).const_mul _))
          ((integrable_finsetSum _ (fun n _ => hiR n)).const_mul _)
        intro u
        dsimp only [W, K]
        rw [← mul_sum, ← mul_assoc]
        exact hwindow hδ.le u
      _ = C * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 *
          ∫ u : ℝ, K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => (1 : ℝ)) u := by
        rw [integral_const_mul, integral_finsetSum _ (fun n _ => hiR n)]
        congr 1
        apply sum_congr rfl
        intro n _
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with u
        by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n)
        · simp [hu]; ring
        · simp [hu]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply sum_le_sum
        intro n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hb := mellin_window_weight_bound (Real.log n) ((Q : ℝ) ^ 2) hδ.le hδ1
        rw [Real.exp_log hnpos] at hb
        dsimp [K]
        have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖a n‖)
        nlinarith
  let δ : ℝ := 1 / T
  have hTpos : 0 < T := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_one hTpos]; exact hT
  let D : ℝ := Real.pi ^ 3 / (2 * δ ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let W {q : ℕ} (χ : DirichletCharacter ℂ q) :=
    ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
  have htime {q : ℕ} (χ : DirichletCharacter ℂ q) :
      (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) ≤ D * W χ := by
    rw [characterPolynomial_time_integral]
    have hnear : δ * (T / (2 * Real.pi)) ≤ 1 / 2 := by
      dsimp [δ]
      have he : (1 / T) * (T / (2 * Real.pi)) = 1 / (2 * Real.pi) := by field_simp
      rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Real.pi_gt_three]
    have hh := gallagher_window_smoothing (Finset.Icc 1 N) (fun n => a n * χ n)
      (fun n => Real.log n) hδ (div_nonneg hTpos.le (by positivity)) hnear
    apply (mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).trans_eq
    dsimp [D, W]
    ring
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), D * W χ := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun χ _ => htime χ)) (hw q hq)
    _ = D * (∑ q ∈ Finset.Icc 1 Q, weight q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), W χ) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro χ _
      ring
    _ ≤ D * (C * ∑ n ∈ Finset.Icc 1 N,
        (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hintegrated hδ hδ1) hD
    _ ≤ _ := by
      simp only [mul_sum]
      apply sum_le_sum
      intro n _
      have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hQsq : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
      have he : D * (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) =
          (Real.pi ^ 3 / 2) * T * ((Q : ℝ) ^ 2 + 2) + Real.pi ^ 3 * n := by
        dsimp [D, δ]
        field_simp
      have hmult := mul_le_mul_of_nonneg_left
        (show (Q : ℝ) ^ 2 + 2 ≤ 3 * (Q : ℝ) ^ 2 by linarith)
        (show 0 ≤ (Real.pi ^ 3 / 2) * T by positivity)
      have hrest : 0 ≤ Real.pi ^ 3 * ((Q : ℝ) ^ 2 * T) := by positivity
      have hrest2 : 0 ≤ Real.pi ^ 3 * n := by positivity
      have hb : D * (δ * ((Q : ℝ) ^ 2 + 2) + 2 * δ ^ 2 * n) ≤
          2 * Real.pi ^ 3 * ((Q : ℝ) ^ 2 * T + n) := by rw [he]; nlinarith
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC) (sq_nonneg ‖a n‖)
      convert hh using 1 <;> ring

/-- Gallagher 1970 p.332 Theorem 4 display 16. The rough support hypothesis
is essential. Its finite input is Lemma 4 display 17, proved using imprimitive Gauss sums
and the coprime Moebius over totient lower bound on p.333 displays 18 and 19.
The already proved smoothing for Theorem 3 supplies the time variable argument. -/
theorem gallagher_prime_hybrid_mean_value : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hfinite⟩ := gallagher_rough_finite_sieve
  refine ⟨2 * Real.pi ^ 3 * C, by positivity, ?_⟩
  intro Q hQ T hT N a hrough
  apply hybrid_of_weighted_finite_sieve Q hQ C hC.le (fun q => Real.log ((Q : ℝ) / q))
    _ (hfinite Q hQ) N a hrough hT
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  apply Real.log_nonneg
  rw [le_div_iff₀ hq0, one_mul]
  exact_mod_cast (Finset.mem_Icc.mp hq).2


/-- LEAF. Gallagher 1970 p.336, passage from Theorem 5 to display 25 and then
Theorem 6 display 24. CONDITIONAL ON the supplied L1 detector and rough hybrid bound.
The remaining proof requires the local zero count from p.333 and the interval covering
and integration argument on p.336, including the bounded principal low height contribution.
The original polynomial region and Page strip are not repeated in this input. -/
theorem gallagher_density_from_detector_and_prime_hybrid
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y)
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  sorry


/-- LEAF. Gallagher 1970, A large sieve density estimate near sigma equals one,
Inventiones 11 pp.329 to 339, Theorem 6. Montgomery and Vaughan 1975 p.366 Section 7.
Gallagher 1975 p.131 display 14. The polynomial range at most three quarters and the
fixed Page strip are proved separately. Only the intervening band remains. -/
theorem gallagher_density_transition : ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  exact gallagher_density_from_detector_and_prime_hybrid
    gallagher_zero_detector gallagher_prime_hybrid_mean_value

/-- Gallagher 1975 p.131. Auxiliary obstruction to removing a logarithmic density loss
uniformly in the band below a Page strip. This is not a counterexample to the density theorem. -/
theorem logarithmic_loss_not_uniformly_absorbable (b : ℝ) (hb : 0 < b) (c C : ℝ) :
    ∃ T σ : ℝ, 2 ≤ T ∧ 3 / 4 < σ ∧ σ < 1 - b / Real.log T ∧
      C * T ^ (c * (1 - σ)) < Real.log T := by
  let x : ℝ := max (max (Real.log 2 + 1) (8 * b + 1))
    (C * Real.exp (2 * b * c) + 1)
  have hxlog : Real.log 2 + 1 ≤ x :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hxb : 8 * b + 1 ≤ x :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hxC : C * Real.exp (2 * b * c) + 1 ≤ x := le_max_right _ _
  have hx : 0 < x := by linarith
  have hxne : x ≠ 0 := hx.ne'
  have hbdiv : 0 < b / x := div_pos hb hx
  refine ⟨Real.exp x, 1 - 2 * b / x, ?_, ?_, ?_, ?_⟩
  · calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  · have hsmall : 2 * b / x < 1 / 4 := (div_lt_iff₀ hx).mpr (by nlinarith)
    linarith
  · rw [Real.log_exp, mul_div_assoc]
    linarith
  · rw [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have he : x * (c * (1 - (1 - 2 * b / x))) = 2 * b * c := by
      field_simp
      ring
    rw [he]
    linarith

/-- LEAF. Gallagher 1970, A large sieve density estimate near sigma equals one,
Inventiones 11 pp.329 to 339. Montgomery and Vaughan 1975 Section 7.
Gallagher 1975 p.131 display 14. The primitive family count inside a fixed Page strip
is proved separately. Only zeros strictly below that strip remain in this input. -/
theorem gallagher_density_away_from_one : ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  intro b hb
  obtain ⟨c, C, hc, hC, h⟩ := gallagher_density_transition b hb
  obtain ⟨D, hD, haway⟩ := density_sum_away_from_one
  refine ⟨max c 16, max C D, lt_max_of_lt_left hc,
    hC.trans (le_max_left _ _), fun T hT σ hσ hσb => ?_⟩
  have hσ1 : σ < 1 := by
    have hl : 0 < Real.log T := Real.log_pos (by linarith)
    have := div_pos hb hl
    linarith
  have hp (d : ℝ) (hd : d ≤ max c 16) :
      T ^ (d * (1 - σ)) ≤ T ^ (max c 16 * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith)
      (mul_le_mul_of_nonneg_right hd (by linarith))
  by_cases hs : σ ≤ 3 / 4
  · exact (haway T hT σ hσ hs).trans
      (mul_le_mul (le_max_right C D) (hp 16 (le_max_right c 16)) (by positivity)
        (hD.trans (le_max_right _ _)))
  · exact (h T hT σ (lt_of_not_ge hs) hσb).trans
      (mul_le_mul (le_max_left C D) (hp c (le_max_left c 16)) (by positivity)
        (hC.trans (le_max_left _ _)))

/-- LEAF. Gallagher 1970, A large sieve density estimate near sigma equals one,
Inventiones 11 pp.329 to 339. Montgomery and Vaughan 1975 Section 7.
Gallagher 1975 p.131 display 14.
The endpoint sigma one is proved separately by nonvanishing. -/
theorem gallagher_density_lt_one : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  obtain ⟨b, hb, hpage⟩ := density_sum_in_page_strip
  obtain ⟨c, C, hc, hC, hbound⟩ := gallagher_density_away_from_one b hb
  refine ⟨c, max C 1, hc, (by linarith [le_max_right C (1 : ℝ)]), fun T hT σ hσ hσ1 => ?_⟩
  have hp : 1 ≤ T ^ (c * (1 - σ)) :=
    Real.one_le_rpow (by linarith) (mul_nonneg hc.le (by linarith))
  by_cases hs : σ < 1 - b / Real.log T
  · exact (hbound T hT σ hσ hs).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity))
  · have hh := hpage T hT σ (le_of_not_gt hs)
    apply hh.trans
    have hmul := mul_le_mul (le_max_right C (1 : ℝ)) hp zero_le_one
      (show 0 ≤ max C 1 by linarith [le_max_right C (1 : ℝ)])
    simpa using hmul

/-- LEAF. Unit U-1532. Gallagher's density estimate for zeros near `σ = 1`: for `T ≥ 2` and
`1/2 ≤ σ ≤ 1`, the zeros with `Re ρ ≥ σ`, `|Im ρ| ≤ T` of all `L(s, χ)`, `χ` primitive of
conductor at most `T`, number at most `C T^{c(1-σ)}`; the input to display (14), p. 131, by the
method of §7 of the 1970 large sieve density paper. -/
theorem gallagher_density : ∃ c C : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  classical
  obtain ⟨c, C, hc, hC, h⟩ := gallagher_density_lt_one
  refine ⟨c, C, hc, ?_⟩
  intro T hT σ hσ hσ1
  by_cases hs : σ = 1
  · subst σ
    rw [density_sum_at_one]
    simpa using hC
  · exact h T hT σ hσ (lt_of_le_of_ne hσ1 hs)

/-- LEAF. Unit U-1532. Lemma 6, display (6) p. 134, for g = 2 where `D/φ(D) = 2`: for
`k ≥ 2` and `N ≥ N_k`, `Σ_{n ≠ 0} r_{k,k}(n) 𝔖(n) = 2 L^{2k} (1 + O(log² k / k))`. -/
theorem lemma6 : ∃ C : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ‖∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x) -
        2 * ((Nat.log 2 N : ℕ) : ℂ) ^ (2 * k)‖ ≤
      C * (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C, hC, hfinite⟩ := finite_singular_main_bound
  refine ⟨C + 1, fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have ha : 0 < Real.log k ^ 2 / k := div_pos (sq_pos_of_pos hlk) hk0
  obtain ⟨N0, htail⟩ := tuple_truncation_eventually (k := k) (by omega) ha
  refine ⟨max N0 (2 ^ k), fun N hN => ?_⟩
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hNk : 2 ^ k ≤ N := (le_max_right _ _).trans hN
  have ht := htail N hN0
  have hf := hfinite k N hk hNk
  let F : ℂ := ∑ q ∈ Icc 1 ⌈(N : ℝ) ^ ((k : ℝ)⁻¹)⌉₊,
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, ramanujanSum q (dif x)
  calc
    _ ≤ ‖(∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x)) - F‖ +
        ‖F - 2 * (Nat.log 2 N : ℂ) ^ (2 * k)‖ := norm_sub_le_norm_sub_add_norm_sub _ F _
    _ ≤ (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) +
        C * (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) := add_le_add ht hf
    _ = _ := by ring

end LeanLab.Linnik.Decomp1532b
