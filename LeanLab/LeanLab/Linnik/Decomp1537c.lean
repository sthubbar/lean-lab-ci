/-
Unit U-1537, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0035, J. Pintz and I. Z. Ruzsa 2020, On Linnik's approximation to Goldbach's problem II,
Acta Math. Hungar. Read from the PC copy copies/P0035.pdf, page numbers as printed; page images
of pp. 9 and 11 checked.

File c: the circle method bookkeeping of Section 4, Lemma 5 on p. 8 with its proof (4.4) to (4.7)
on p. 9, and of Section 6, Lemma 9 on p. 10 with its proof (6.2) to (6.5) on p. 11, and the end of
the proof of Theorem 1, (6.6) to (6.11) on pp. 11 and 12.

Concrete objects, all for fixed `N, N₁, L, P, Q`:
* `ee x = e(x) = exp(2πix)`; `Ssum = S(α)`, (2.1) p. 3, over primes `p ∈ (N₁, N]`;
  `Gsum = G(α) = ∑_{ν=1}^{L} e(2^ν α)`, (2.8) p. 3.
* `rk' n = r'_k(n)`, (2.3) p. 3; `rkk m = r_{k,k}(m)`, (2.4) p. 3; `rK'' = r''_{2k}(N)`, (2.2) p. 3;
  exponents `ν ∈ [1, L]` are written `ν i + 1` with `ν i : Fin L`.
* `majorArcs P Q = 𝔐`, (2.6) p. 2; `Ufull Q = (1/Q, 1 + 1/Q]`, the period of (2.7);
  `C(𝔐) = Ufull Q \ majorArcs P Q`; `R1 h = R₁(h)`, (2.11) p. 3; `S2 = S₂(N)`, (4.2) p. 8.
* `sing c0 h = 𝔖(h) = 2 c₀ ∏_{p | h, p > 2}(1 + 1/(p - 2))`, (2.13) p. 4, with `c₀ = C₀` in the
  paper; `𝔖(0) = 0` by convention, as the sums of the paper over `h ≠ 0` need.
* `star L` is the index set `1 ≤ ν₁ < ν₂ ≤ L` of `∑*`, p. 9; `hdiff (ν₁, ν₂) = 2^{ν₂} - 2^{ν₁}`.

Inputs from other papers enter the assemblies as hypotheses, named in each docstring: part I
[PR] Lemma 10 (Lemma 4 here), (8.8) to (8.14) (display (4.6) here), Corollary 2 (Lemma 6 here),
Lemma 12 (Lemma 8 here), Khalfalah-Pintz (Lemma 7 here), Vinogradov (Lemma 2 here), the prime
number theorem (6.6), and Corollary 1 as the per `h` bounds on `R₁(h)`, see `Decomp1537b`.

Assemblies, CONDITIONAL ON the leaves below and on the stated inputs, no sorry of their own:
`identity44`, `lemma5_of_leaves`, `lemma5_bad_bound`, `weighted_split`, `lemma9_of_leaves`,
`lemma9_bad_bound`, `final_positivity`, `k4_positive`, `k4_representation`.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
/-
CODEX task170 completed every original LEAF proof. The dependency labels above record the original
decomposition. The analytic assemblies retain their explicit cited input hypotheses. AI wrote these proofs.
-/
import Mathlib
import LeanLab.Linnik.U7206Display6
import LeanLab.Linnik.Decomp1537a
import LeanLab.Linnik.PR2020

namespace LeanLab.Linnik.Decomp1537c

open Finset Real MeasureTheory
open LeanLab.Linnik.Decomp1537a (sfac sfac_nonneg lemma1_class oddSqf)

/-! ### Definitions -/

/-- `e(x) = exp(2πix)`, (2.1) p. 3. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- The primes `p ∈ (N₁, N]`. -/
def primesIn (N1 N : ℕ) : Finset ℕ := (Ioc N1 N).filter Nat.Prime

/-- `S(α) = ∑_{N₁ < p ≤ N} log p e(pα)`, (2.1) p. 3. -/
noncomputable def Ssum (N1 N : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ primesIn N1 N, (Real.log p : ℂ) * ee (p * α)

/-- `G(α) = ∑_{ν=1}^{L} e(2^ν α)`, (2.8) p. 3. -/
noncomputable def Gsum (L : ℕ) (α : ℝ) : ℂ := ∑ ν ∈ Icc 1 L, ee (2 ^ ν * α)

/-- `2^{ν₁} + ... + 2^{ν_k}` with exponents `ν i + 1 ∈ [1, L]`. -/
def svv {k L : ℕ} (ν : Fin k → Fin L) : ℕ := ∑ i, 2 ^ ((ν i : ℕ) + 1)

/-- Pairs of exponent tuples. -/
abbrev pairs (k L : ℕ) : Type := (Fin k → Fin L) × (Fin k → Fin L)

/-- `2^{ν₁} + ... + 2^{ν_k} - 2^{μ₁} - ... - 2^{μ_k}`, (2.4) p. 3. -/
def difc {k L : ℕ} (x : pairs k L) : ℤ := (svv x.1 : ℤ) - svv x.2

/-- `r'_k(n) = ∑_{n = p + 2^{ν₁} + ... + 2^{ν_k}} log p`, (2.3) p. 3. -/
noncomputable def rk' (N1 N k L n : ℕ) : ℝ :=
  ∑ p ∈ primesIn N1 N, ∑ ν : Fin k → Fin L, if p + svv ν = n then Real.log p else 0

/-- `r_{k,k}(m)`, (2.4) p. 3. -/
def rkk (k L : ℕ) (m : ℤ) : ℕ := (univ.filter (fun x : pairs k L => difc x = m)).card

/-- `r''_{2k}(N) = ∑_{N = p₁ + p₂ + 2^{ν₁} + ... + 2^{ν_{2k}}} log p₁ log p₂`, (2.2) p. 3. -/
noncomputable def rK'' (N1 N k L : ℕ) : ℝ :=
  ∑ p₁ ∈ primesIn N1 N, ∑ p₂ ∈ primesIn N1 N, ∑ ν : Fin (2 * k) → Fin L,
    if p₁ + p₂ + svv ν = N then Real.log p₁ * Real.log p₂ else 0

/-- `𝔖(h)`, (2.13) p. 4, with the constant `c₀` as a parameter, and `𝔖(0) = 0`. -/
noncomputable def sing (c0 : ℝ) (h : ℤ) : ℝ := if h = 0 then 0 else 2 * c0 * sfac h

/-- The major arcs `𝔐`, (2.6) p. 2. -/
def majorArcs (P Q : ℝ) : Set ℝ :=
  ⋃ q ∈ {q : ℕ | 1 ≤ q ∧ (q : ℝ) ≤ P}, ⋃ a ∈ {a : ℕ | 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q},
    Set.Icc ((a : ℝ) / q - 1 / (q * Q)) ((a : ℝ) / q + 1 / (q * Q))

/-- The period `(1/Q, 1 + 1/Q]` of (2.7) p. 2. -/
def Ufull (Q : ℝ) : Set ℝ := Set.Ioc (1 / Q) (1 + 1 / Q)

/-- `R₁(h) = ∫_𝔐 |S(α)|² e(-hα) dα`, (2.11) p. 3. -/
noncomputable def R1 (N1 N : ℕ) (P Q : ℝ) (h : ℤ) : ℂ :=
  ∫ α in majorArcs P Q ∩ Ufull Q, ((‖Ssum N1 N α‖ ^ 2 : ℝ) : ℂ) * ee (-(h * α))

/-- `S₂(N) = ∫_{C(𝔐)} |S(α) G(α)|² dα`, (4.2) p. 8. -/
noncomputable def S2 (N1 N L : ℕ) (P Q : ℝ) : ℝ :=
  ∫ α in Ufull Q \ majorArcs P Q, ‖Ssum N1 N α * Gsum L α‖ ^ 2

/-- The index set `1 ≤ ν₁ < ν₂ ≤ L` of `∑*`, p. 9. -/
def star (L : ℕ) : Finset (ℕ × ℕ) := ((Icc 1 L) ×ˢ (Icc 1 L)).filter (fun x => x.1 < x.2)

/-- `2^{ν₂} - 2^{ν₁}`. -/
def hdiff (x : ℕ × ℕ) : ℤ := 2 ^ x.2 - 2 ^ x.1

/-- The bound `k 2^{L+1}` on `|m|` for `r_{k,k}(m) ≠ 0`. -/
def Bk (k L : ℕ) : ℤ := ((k * 2 ^ (L + 1) : ℕ) : ℤ)

/-- The range `[-k 2^{L+1}, k 2^{L+1}]` of `m` in (6.3) p. 11. -/
def mset (k L : ℕ) : Finset ℤ := Icc (-Bk k L) (Bk k L)

/-! ### Small proved facts -/

lemma majorArcs_measurable (P Q : ℝ) : MeasurableSet (majorArcs P Q) := by
  unfold majorArcs
  exact MeasurableSet.biUnion (Set.to_countable _) fun q _ =>
    MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurableSet_Icc

lemma minor_measurable (P Q : ℝ) : MeasurableSet (Ufull Q \ majorArcs P Q) :=
  measurableSet_Ioc.diff (majorArcs_measurable P Q)

lemma sing_nonneg {c0 : ℝ} (hc0 : 0 ≤ c0) (h : ℤ) : 0 ≤ sing c0 h := by
  unfold sing
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg (by positivity) (sfac_nonneg h)

lemma sing_le {c0 : ℝ} (hc0 : 0 ≤ c0) (hc1 : c0 ≤ 1) (h : ℤ) : sing c0 h ≤ 2 * sfac h := by
  unfold sing
  have := sfac_nonneg h
  split_ifs
  · positivity
  · nlinarith

/-- LEAF. Unit U-1537. Sums weighted by `r_{k,k}` are sums over pairs, as in (5.2) p. 10 and
(6.3) p. 11: `∑_m r_{k,k}(m) g(m) = ∑_{(ν, μ)} g(2^{ν₁} + ... - 2^{μ_k})`. -/
theorem rkk_sum_eq (k L : ℕ) (g : ℤ → ℝ) :
    ∑ m ∈ mset k L, (rkk k L m : ℝ) * g m = ∑ x : pairs k L, g (difc x) := by
  have hb (ν : Fin k → Fin L) : svv ν ≤ k * 2 ^ (L + 1) := by
    unfold svv
    calc
      ∑ i, 2 ^ ((ν i : ℕ) + 1) ≤ ∑ _i : Fin k, 2 ^ (L + 1) :=
        sum_le_sum fun i _ => Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = _ := by simp
  have hm : ∀ x ∈ (univ : Finset (pairs k L)), difc x ∈ mset k L := by
    intro x _
    have h1 : (svv x.1 : ℤ) ≤ (k * 2 ^ (L + 1) : ℕ) := by exact_mod_cast hb x.1
    have h2 : (svv x.2 : ℤ) ≤ (k * 2 ^ (L + 1) : ℕ) := by exact_mod_cast hb x.2
    simp only [mset, mem_Icc, difc, Bk]
    constructor <;> omega
  rw [← sum_fiberwise_of_maps_to hm (fun x => g (difc x))]
  apply sum_congr rfl
  intro m _
  calc
    _ = ∑ x ∈ univ.filter (fun x : pairs k L => difc x = m), g m := by
      simp [rkk, nsmul_eq_mul]
    _ = _ := sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]

/-- The finite Fourier expansion of the even moment of G. P0035 p.11 display 6.3. -/
theorem Gsum_norm_pow_expand (k L : ℕ) (α : ℝ) :
    ‖Gsum L α‖ ^ (2 * k) = ∑ x : pairs k L, (ee (-((difc x : ℝ) * α))).re := by
  have hconj (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
    simpa only [ee, LeanLab.Linnik.U1412Display53.eC, LeanLab.Linnik.U1434Lemma21.e_eq_eC] using
      (LeanLab.PNTPort.LargeSieve.e_neg x).symm
  have hpow : Gsum L α ^ k = ∑ ν : Fin k → Fin L, ee (svv ν * α) :=
    LeanLab.Linnik.U1434Lemma21.Gs_pow k L α
  have hn : ((‖Gsum L α‖ ^ (2 * k) : ℝ) : ℂ) =
      (starRingEnd ℂ) (Gsum L α ^ k) * Gsum L α ^ k := by
    conv_rhs => rw [mul_comm]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  have hh : (starRingEnd ℂ) (Gsum L α ^ k) * Gsum L α ^ k =
      ∑ x : pairs k L, ee (-((difc x : ℝ) * α)) := by
    rw [hpow, map_sum, sum_mul_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun ν _ => sum_congr rfl fun μ _ => ?_
    rw [hconj]
    change LeanLab.Linnik.U1412Display53.eC _ * LeanLab.Linnik.U1412Display53.eC _ =
      LeanLab.Linnik.U1412Display53.eC _
    rw [← LeanLab.Linnik.U1434Lemma21.eC_add]
    congr 1
    simp only [difc, Int.cast_sub, Int.cast_natCast]
    ring
  have hh' := congrArg Complex.re (hn.trans hh)
  simpa only [Complex.ofReal_re, Complex.re_sum] using hh'

/-! ### Leaves: Parseval, the arcs, and `R₁` -/

/-- LEAF. Unit U-1537. Parseval over one period, (4.1) p. 8 and (6.2) p. 11:
`∫_0^1 |S(α) G(α)^k|² dα = ∑_n r'_k(n)²`, since `S G^k = ∑_n r'_k(n) e(nα)` with
`n ≤ N + k 2^L`. -/
theorem parseval_k (N1 N k L : ℕ) (Q : ℝ) :
    ∫ α in Ufull Q, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2 =
      ∑ n ∈ range (N + k * 2 ^ (L + 1) + 1), (rk' N1 N k L n) ^ 2 := by
  let R := N + k * 2 ^ (L + 1) + 1
  have hs (α : ℝ) : Ssum N1 N α = LeanLab.Linnik.U1426ChainWire.Sm N1 N α := by
    unfold Ssum LeanLab.Linnik.U1426ChainWire.Sm LeanLab.Linnik.LiLiuLemma43.SA
    simp only [LeanLab.Linnik.U1434Lemma21.e_eq_eC]
    rfl
  have hrep (α : ℝ) : Ssum N1 N α * Gsum L α ^ k =
      LeanLab.Linnik.LiLiuLemma43.SA (range R) (fun n => (rk' N1 N k L n : ℂ)) α := by
    rw [hs]
    exact LeanLab.Linnik.U1434Lemma21.SG_pow k N1 N L R (by
      dsimp [R]
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_succ L)
      simp only [Nat.succ_eq_add_one] at this
      have := Nat.mul_le_mul_left k this
      omega) α
  simp_rw [hrep]
  have hp : Function.Periodic (fun α =>
      ‖LeanLab.Linnik.LiLiuLemma43.SA (range R) (fun n => (rk' N1 N k L n : ℂ)) α‖ ^ 2) 1 := by
    intro x
    dsimp only
    rw [LeanLab.Linnik.LiLiuLemma43Int.SA_periodic]
  have he := hp.intervalIntegral_add_eq (1 / Q) 0
  simp only [zero_add] at he
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le zero_le_one] at he
  have hparse : ∫ α in Set.Ioc (0 : ℝ) 1,
      ‖LeanLab.Linnik.LiLiuLemma43.SA (range R) (fun n => (rk' N1 N k L n : ℂ)) α‖ ^ 2 =
      ∑ n ∈ range R, rk' N1 N k L n ^ 2 := by
    rw [← integral_Icc_eq_integral_Ioc]
    exact LeanLab.Linnik.U1426ChainWire.parseval _ _
  simpa [R, Ufull, add_comm] using he.trans hparse

/-- LEAF. Unit U-1537. The three way split of (6.2) p. 11, `∫_0^1 = ∫_𝔐 + ∫_{C(𝔐) ∩ E*} +
∫_{C(𝔐) ∖ E*}`, for a measurable `E*`; with `E* = ∅` it is the split `∫_0^1 - ∫_𝔐` of (4.4) p. 9. -/
theorem split3 (N1 N k L : ℕ) (P Q : ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    ∫ α in Ufull Q, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2 =
      (∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2) +
      (∫ α in (Ufull Q \ majorArcs P Q) ∩ E, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2) +
      ∫ α in (Ufull Q \ majorArcs P Q) \ E, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2 := by
  have hc : Continuous (fun α => ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2) := by
    unfold Ssum Gsum ee
    fun_prop
  have hI : IntegrableOn (fun α => ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2) (Ufull Q) :=
    hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hM : MeasurableSet (majorArcs P Q) := by
    unfold majorArcs
    exact MeasurableSet.biUnion (Set.to_countable _) fun q _ =>
      MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurableSet_Icc
  have h1 := integral_inter_add_sdiff hM hI
  have h2 := integral_inter_add_sdiff (s := Ufull Q \ majorArcs P Q) hE (hI.mono_set Set.diff_subset)
  rw [Set.inter_comm] at h1
  linarith

/-- LEAF. Unit U-1537. The first line of (6.3) p. 11, and with `k = 1` the middle of (4.4) p. 9:
`∫_𝔐 |S|² |G|^{2k} = ∑_m r_{k,k}(m) R₁(m)`, real parts, since `|G^k|² = ∑_m r_{k,k}(m) e(mα)` and
`r_{k,k}(-m) = r_{k,k}(m)`. -/
theorem major_expand (N1 N k L : ℕ) (P Q : ℝ) :
    ∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α‖ ^ 2 * ‖Gsum L α‖ ^ (2 * k) =
      ∑ m ∈ mset k L, (rkk k L m : ℝ) * (R1 N1 N P Q m).re := by
  have hsub : majorArcs P Q ∩ Ufull Q ⊆ Set.Icc (1 / Q) (1 + 1 / Q) :=
    fun α hα => Set.Ioc_subset_Icc_self hα.2
  have hi (m : ℤ) : IntegrableOn
      (fun α => ((‖Ssum N1 N α‖ ^ 2 : ℝ) : ℂ) * ee (-(m * α)))
      (majorArcs P Q ∩ Ufull Q) := by
    have hc : Continuous (fun α : ℝ => ((‖Ssum N1 N α‖ ^ 2 : ℝ) : ℂ) * ee (-(m * α))) := by
      unfold Ssum ee; fun_prop
    exact hc.integrableOn_Icc.mono_set hsub
  have hint (m : ℤ) : IntegrableOn
      (fun α => ‖Ssum N1 N α‖ ^ 2 * (ee (-(m * α))).re) (majorArcs P Q ∩ Ufull Q) := by
    simpa only [RCLike.re_to_complex, Complex.re_ofReal_mul] using (hi m).re
  have hr (m : ℤ) :
      (∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α‖ ^ 2 * (ee (-(m * α))).re) =
        (R1 N1 N P Q m).re := by
    simpa only [R1, RCLike.re_to_complex, Complex.re_ofReal_mul] using integral_re (hi m)
  rw [rkk_sum_eq]
  simp_rw [Gsum_norm_pow_expand, mul_sum]
  rw [integral_finsetSum _ (fun x _ => hint (difc x))]
  exact sum_congr rfl fun x _ => hr (difc x)

/-- LEAF. Unit U-1537. The second line of (6.3) p. 11: `R₁(0) = ∫_𝔐 |S|² ≤ ∫_0^1 |S|² =
∑_{N₁ < p ≤ N} log² p`. -/
theorem R1_zero_re_le (N1 N : ℕ) (P Q : ℝ) :
    (R1 N1 N P Q 0).re ≤ ∑ p ∈ primesIn N1 N, Real.log p ^ 2 := by
  have hc : Continuous (fun α => ‖Ssum N1 N α‖ ^ 2) := by unfold Ssum ee; fun_prop
  have hi : IntegrableOn (fun α => ‖Ssum N1 N α‖ ^ 2) (Ufull Q) :=
    hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hs (α : ℝ) : Ssum N1 N α =
      LeanLab.Linnik.LiLiuLemma43.SA (primesIn N1 N) (fun p => (Real.log p : ℂ)) α := by
    unfold Ssum LeanLab.Linnik.LiLiuLemma43.SA
    simp only [LeanLab.Linnik.U1434Lemma21.e_eq_eC]
    rfl
  have hp : Function.Periodic (fun α => ‖Ssum N1 N α‖ ^ 2) 1 := by
    intro x
    dsimp only
    simp only [hs, LeanLab.Linnik.LiLiuLemma43Int.SA_periodic]
  have he := hp.intervalIntegral_add_eq (1 / Q) 0
  simp only [zero_add] at he
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le zero_le_one] at he
  have hparse : ∫ α in Set.Ioc (0 : ℝ) 1, ‖Ssum N1 N α‖ ^ 2 =
      ∑ p ∈ primesIn N1 N, Real.log p ^ 2 := by
    simp_rw [hs]
    rw [← integral_Icc_eq_integral_Ioc]
    exact LeanLab.Linnik.U1426ChainWire.parseval _ _
  have hfull : ∫ α in Ufull Q, ‖Ssum N1 N α‖ ^ 2 =
      ∑ p ∈ primesIn N1 N, Real.log p ^ 2 := by
    simpa [Ufull, add_comm] using he.trans hparse
  have hr : (R1 N1 N P Q 0).re = ∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α‖ ^ 2 := by
    have h0 : ee 0 = 1 := by simp [ee]
    simp only [R1, Int.cast_zero, zero_mul, neg_zero, h0, mul_one]
    have hh : (∫ α in majorArcs P Q ∩ Ufull Q, ((‖Ssum N1 N α‖ ^ 2 : ℝ) : ℂ)) =
        ((∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
    rw [hh]
    rfl
  rw [hr, ← hfull]
  exact setIntegral_mono_set (s := majorArcs P Q ∩ Ufull Q) hi
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun α (hα : α ∈ majorArcs P Q ∩ Ufull Q) => hα.2)

/-- LEAF. Unit U-1537. `∑_{p ≤ N} log² p ≤ 2N log N`, the factor `2N log N` in the third line
of (6.3) p. 11, from `θ(N) ≤ N log 4`. -/
theorem sum_log_sq_le (N1 N : ℕ) :
    ∑ p ∈ primesIn N1 N, Real.log p ^ 2 ≤ 2 * N * Real.log N := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc
    ∑ p ∈ primesIn N1 N, Real.log p ^ 2 ≤
        ∑ p ∈ primesIn N1 N, Real.log p * Real.log N := by
      apply sum_le_sum
      intro p hp
      have hpN := (mem_Ioc.mp (mem_filter.mp hp).1).2
      have hp0 := (mem_filter.mp hp).2.pos
      have hlog := Real.log_le_log (x := (p : ℝ)) (y := (N : ℝ)) (by exact_mod_cast hp0) (by exact_mod_cast hpN)
      nlinarith [mul_le_mul_of_nonneg_left hlog (Real.log_natCast_nonneg p)]
    _ = (∑ p ∈ primesIn N1 N, Real.log p) * Real.log N := by rw [sum_mul]
    _ ≤ Chebyshev.theta N * Real.log N := by
      apply mul_le_mul_of_nonneg_right _ hlogN
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := mem_filter.mp hp
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := hp'.2.pos; omega,
          by simpa using (mem_Ioc.mp hp'.1).2⟩, hp'.2⟩
      · intro p _ _; exact Real.log_natCast_nonneg p
    _ ≤ (Real.log 4 * N) * Real.log N :=
      mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) hlogN
    _ ≤ 2 * N * Real.log N := by
      have h4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have h2 : Real.log 2 ≤ 1 := by
          have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        norm_num only [Nat.cast_ofNat]
        linarith
      gcongr

/-- LEAF. Unit U-1537. `R₁(0) = ∫_𝔐 |S|² ≥ 0`, used for "by `R₁(0) > 0`" before (4.7) p. 9. -/
theorem R1_zero_re_nonneg (N1 N : ℕ) (P Q : ℝ) : 0 ≤ (R1 N1 N P Q 0).re := by
  dsimp [R1]
  have h1 : (0:ℤ) = (0:ℝ) := by exact Int.cast_zero
  simp only [h1, zero_mul, neg_zero]
  have h2 : ee 0 = 1 := by
    dsimp [ee]
    simp
  simp only [h2, mul_one]
  have h3 : ∫ (α : ℝ) in majorArcs P Q ∩ Ufull Q, (↑(‖Ssum N1 N α‖ ^ 2) : ℂ) = ↑(∫ (α : ℝ) in majorArcs P Q ∩ Ufull Q, (‖Ssum N1 N α‖ ^ 2 : ℝ)) := by
    exact integral_ofReal
  rw [h3]
  have h4 : (↑(∫ (α : ℝ) in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α‖ ^ 2) : ℂ).re = ∫ (α : ℝ) in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α‖ ^ 2 := by
    exact Complex.ofReal_re _
  rw [h4]
  apply integral_nonneg
  intro α
  positivity

/-- LEAF. Unit U-1537. The right side of (4.4) p. 9: for `k = 1`,
`∑_m r_{1,1}(m) R₁(m) = L R₁(0) + 2 ∑_{ν₁ < ν₂} R₁(2^{ν₂} - 2^{ν₁})`, real parts, using
`Re R₁(-h) = Re R₁(h)`. -/
theorem pair_k1 (N1 N L : ℕ) (P Q : ℝ) :
    ∑ m ∈ mset 1 L, (rkk 1 L m : ℝ) * (R1 N1 N P Q m).re =
      L * (R1 N1 N P Q 0).re + 2 * ∑ x ∈ star L, (R1 N1 N P Q (hdiff x)).re := by
  let M := majorArcs P Q ∩ Ufull Q
  let I := Icc 1 L
  let F (a b : ℕ) := (R1 N1 N P Q ((2 : ℤ) ^ b - 2 ^ a)).re
  have hi (h : ℤ) : IntegrableOn
      (fun α => ((‖Ssum N1 N α‖ ^ 2 : ℝ) : ℂ) * ee (-(h * α))) M := by
    have hc : Continuous (fun α : ℝ => ((‖Ssum N1 N α‖ ^ 2 : ℝ) : ℂ) * ee (-(h * α))) := by
      unfold Ssum ee; fun_prop
    exact hc.integrableOn_Icc.mono_set (fun α hα => Set.Ioc_subset_Icc_self hα.2)
  have hint (h : ℤ) : IntegrableOn
      (fun α => ‖Ssum N1 N α‖ ^ 2 * (ee (-(h * α))).re) M := by
    simpa only [RCLike.re_to_complex, Complex.re_ofReal_mul] using (hi h).re
  have hr (h : ℤ) : (∫ α in M, ‖Ssum N1 N α‖ ^ 2 * (ee (-(h * α))).re) =
      (R1 N1 N P Q h).re := by
    simpa only [R1, RCLike.re_to_complex, Complex.re_ofReal_mul] using integral_re (hi h)
  have heven (x : ℝ) : (ee (-x)).re = (ee x).re := by
    change (LeanLab.Linnik.U1412Display53.eC (-x)).re = (LeanLab.Linnik.U1412Display53.eC x).re
    simp only [← LeanLab.Linnik.U1434Lemma21.e_eq_eC, LeanLab.PNTPort.LargeSieve.e_neg, Complex.conj_re]
  have hsym (a b : ℕ) : F a b = F b a := by
    dsimp [F]
    rw [← hr, ← hr]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro α
    have hh : -((((2 : ℤ) ^ a - 2 ^ b : ℤ) : ℝ) * α) =
        -(-((((2 : ℤ) ^ b - 2 ^ a : ℤ) : ℝ) * α)) := by push_cast; ring
    dsimp only
    rw [hh, heven]
    simp only [neg_neg]
  have hdiag (a : ℕ) : F a a = (R1 N1 N P Q 0).re := by simp [F]
  have hex : ∫ α in M, ‖Ssum N1 N α‖ ^ 2 * ‖Gsum L α‖ ^ 2 = ∑ a ∈ I, ∑ b ∈ I, F a b := by
    have hG (α : ℝ) : ‖Gsum L α‖ ^ 2 =
        ∑ a ∈ I, ∑ b ∈ I, (ee (-((((2 : ℤ) ^ b - 2 ^ a : ℤ) : ℝ) * α))).re := by
      have hh := LeanLab.Linnik.U7205Display34.normG_sq L α
      change ‖Gsum L α‖ ^ 2 = _ at hh
      rw [hh]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      change (ee (((2 : ℝ) ^ a - 2 ^ b) * α)).re = _
      congr 2
      push_cast
      ring
    simp_rw [hG, mul_sum]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hint _)]
    apply sum_congr rfl
    intro a _
    rw [integral_finsetSum _ (fun b _ => hint _)]
    exact sum_congr rfl fun b _ => hr _
  have hsplit : ∑ a ∈ I, ∑ b ∈ I, F a b =
      ∑ a ∈ I, ∑ b ∈ I, ((if a = b then (R1 N1 N P Q 0).re else 0) +
        (if a < b then F a b else 0) + (if b < a then F a b else 0)) := by
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst b; simp [hdiag]
    · simp [h, h.ne', h.not_gt]
  have hupper : (∑ a ∈ I, ∑ b ∈ I, if b < a then F a b else 0) =
      ∑ a ∈ I, ∑ b ∈ I, if a < b then F a b else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rw [hsym b a]
  have hstar : (∑ a ∈ I, ∑ b ∈ I, if a < b then F a b else 0) =
      ∑ x ∈ star L, (R1 N1 N P Q (hdiff x)).re := by
    simp only [star, sum_filter, sum_product, I, hdiff, F]
  rw [← major_expand]
  norm_num only [mul_one]
  rw [hex, hsplit]
  simp_rw [sum_add_distrib]
  rw [hupper, hstar]
  have hD : (∑ a ∈ I, ∑ b ∈ I, if a = b then (R1 N1 N P Q 0).re else 0) =
      L * (R1 N1 N P Q 0).re := by
    simp only [I, sum_ite_eq, mem_Icc]
    rw [sum_ite_of_true (fun a ha => mem_Icc.mp ha)]
    simp
  rw [hD]
  ring

/-- LEAF. Unit U-1537. (6.4) p. 11: on a set `A ⊆ C(𝔐)` where `|G| ≤ c L`, Lemma 6,
`∫_A |S G^k|² ≤ (cL)^{2k-2} ∫_{C(𝔐)} |S G|²`. -/
theorem minor_compare (N1 N k L : ℕ) (P Q : ℝ) (hk : 1 ≤ k) {A : Set ℝ} (hAm : MeasurableSet A)
    (hA : A ⊆ Ufull Q \ majorArcs P Q) {c : ℝ} (hc : 0 ≤ c)
    (hG : ∀ α ∈ A, ‖Gsum L α‖ ≤ c * L) :
    ∫ α in A, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2 ≤ (c * L) ^ (2 * k - 2) * S2 N1 N L P Q := by
  have c1 : Continuous (fun α => ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2) := by
    unfold Ssum Gsum ee; fun_prop
  have c2 : Continuous (fun α => ‖Ssum N1 N α * Gsum L α‖ ^ 2) := by
    unfold Ssum Gsum ee; fun_prop
  have hAU : A ⊆ Set.Icc (1 / Q) (1 + 1 / Q) :=
    fun α hα => Set.Ioc_subset_Icc_self (hA hα).1
  have i1 : IntegrableOn (fun α => ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2) A :=
    c1.integrableOn_Icc.mono_set hAU
  have i2U : IntegrableOn (fun α => ‖Ssum N1 N α * Gsum L α‖ ^ 2)
      (Set.Icc (1 / Q) (1 + 1 / Q)) := c2.integrableOn_Icc
  have hMU : Ufull Q \ majorArcs P Q ⊆ Set.Icc (1 / Q) (1 + 1 / Q) :=
    fun α hα => Set.Ioc_subset_Icc_self hα.1
  have i2 := (i2U.mono_set hAU).const_mul ((c * L) ^ (2 * k - 2))
  calc
    _ ≤ ∫ α in A, (c * L) ^ (2 * k - 2) * ‖Ssum N1 N α * Gsum L α‖ ^ 2 :=
      setIntegral_mono_on i1 i2 hAm fun α hα =>
        LeanLab.Linnik.U7206.pointwise hk (hG α hα)
    _ = (c * L) ^ (2 * k - 2) * ∫ α in A, ‖Ssum N1 N α * Gsum L α‖ ^ 2 :=
      integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_set (i2U.mono_set hMU)
        (Filter.Eventually.of_forall fun _ => by positivity)
        (Filter.Eventually.of_forall fun α hα => hA hα)

/-- LEAF. Unit U-1537. (6.5) p. 11: `∫_{C(𝔐) ∩ E*} |S G^k|² ≤ |E*| sup_{C(𝔐)} |S|² L^{2k}`. The
paper writes `|E*| N^{8/5} L^8`; the factor `L^{2k}` from `|G|^{2k} ≤ L^{2k}` is dropped there,
harmlessly, see QUESTION in PROGRESS.md. -/
theorem E_part (N1 N k L : ℕ) (P Q : ℝ) {E : Set ℝ} (hE : MeasurableSet E)
    (hEf : volume E ≠ ⊤) {Ssup : ℝ} (hS : ∀ α ∈ Ufull Q \ majorArcs P Q, ‖Ssum N1 N α‖ ≤ Ssup) :
    ∫ α in (Ufull Q \ majorArcs P Q) ∩ E, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2 ≤
      (volume E).toReal * Ssup ^ 2 * (L : ℝ) ^ (2 * k) := by
  have hnorm (x : ℝ) : ‖ee x‖ = 1 := by simp [ee, Complex.norm_exp, Complex.mul_re]
  have hG (α : ℝ) : ‖Gsum L α‖ ≤ L := by
    calc
      ‖Gsum L α‖ ≤ ∑ ν ∈ Icc 1 L, ‖ee (2 ^ ν * α)‖ := norm_sum_le _ _
      _ = L := by simp [hnorm]
  let A := (Ufull Q \ majorArcs P Q) ∩ E
  have hfin : volume A < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_right) (lt_top_iff_ne_top.mpr hEf)
  have hb : ∀ α ∈ A, ‖‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2‖ ≤
      Ssup ^ 2 * (L : ℝ) ^ (2 * k) := by
    intro α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, norm_pow, mul_pow,
      show (‖Gsum L α‖ ^ k) ^ 2 = ‖Gsum L α‖ ^ (2 * k) by rw [← pow_mul, Nat.mul_comm]]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hS α hα.1) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hG α) _) (by positivity) (by positivity)
  have hh := norm_setIntegral_le_of_norm_le_const hfin hb
  have hm : (volume A).toReal ≤ (volume E).toReal :=
    ENNReal.toReal_mono hEf (measure_mono Set.inter_subset_right)
  calc
    ∫ α in A, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2 ≤
        ‖∫ α in A, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2‖ := Real.le_norm_self _
    _ ≤ (Ssup ^ 2 * (L : ℝ) ^ (2 * k)) * (volume A).toReal := hh
    _ ≤ (Ssup ^ 2 * (L : ℝ) ^ (2 * k)) * (volume E).toReal :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

/-! ### Leaves: the end of the proof, (6.6) to (6.10) -/

/-- LEAF. Unit U-1537. The first line of (6.9) p. 12: `r''_{2k}(N) = ∑_{m + n = N} r'_k(m) r'_k(n)`,
splitting the `2k` powers of 2 into two groups of `k`. -/
theorem convolution (N1 N k L : ℕ) :
    rK'' N1 N k L = ∑ m ∈ range (N + 1), rk' N1 N k L m * rk' N1 N k L (N - m) := by
  have inner (A B : ℕ) (x y : ℝ) :
      ∑ n ∈ range (N + 1), (if A = n then x else 0) * (if B = N - n then y else 0) =
        if A + B = N then x * y else 0 := by
    simp_rw [ite_mul, zero_mul]
    rw [sum_ite_eq (range (N + 1)) A]
    by_cases hA : A ≤ N
    · rw [if_pos (mem_range.mpr (by omega))]
      by_cases hB : A + B = N
      · rw [if_pos (by omega), if_pos hB, mul_comm]
      · rw [if_neg (by omega), if_neg hB]; simp
    · rw [if_neg (by simp; omega), if_neg (by omega)]
  have split (p q : ℕ) (x : ℝ) :
      (∑ ν : Fin (2 * k) → Fin L, if p + q + svv ν = N then x else 0) =
        ∑ ν1 : Fin k → Fin L, ∑ ν2 : Fin k → Fin L,
          if p + svv ν1 + (q + svv ν2) = N then x else 0 := by
    rw [two_mul, ← Fintype.sum_prod_type', ← (Fin.appendEquiv k k).sum_comp]
    refine Fintype.sum_congr _ _ fun ν => ?_
    have hh : p + q + svv (Fin.appendEquiv k k ν) = p + svv ν.1 + (q + svv ν.2) := by
      simp only [Fin.appendEquiv_apply, svv, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
      ring
    rw [hh]
  unfold rK''
  simp_rw [split]
  unfold rk'
  simp_rw [sum_mul_sum]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun ν1 _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun ν2 _ => ?_
  exact inner _ _ _ _

/-- LEAF. Unit U-1537. `r'_k(n) = 0` for even `n` when `N₁ ≥ 2`: then `p` is odd and the powers of
2 are even; this is why only odd `n` occur in (6.7) to (6.10) p. 12. -/
theorem rk'_even (N1 N k L : ℕ) (hN1 : 2 ≤ N1) {n : ℕ} (hn : Even n) : rk' N1 N k L n = 0 := by
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro ν _
  have hpm := mem_filter.mp hp
  have hpodd : Odd p := hpm.2.odd_of_ne_two (by have := (mem_Ioc.mp hpm.1).1; omega)
  have hs : Even (svv ν) := by
    apply Finset.even_sum
    intro i _
    exact Even.pow_of_ne_zero (by norm_num : Even (2 : ℕ)) (by omega)
  have hne : p + svv ν ≠ n := by
    intro he
    have := hpodd.add_even hs
    rw [he] at this
    exact (Nat.not_even_iff_odd.mpr this) hn
  simp [hne]

/-- LEAF. Unit U-1537. For even `N` there are `N/2` odd `n ≤ N`, the `N/2` in (6.10) p. 12. -/
theorem odd_count {N : ℕ} (hN : Even N) : ((range (N + 1)).filter Odd).card = N / 2 := by
  obtain ⟨n, rfl⟩ := hN
  have he : (range (n + n + 1)).filter Odd = (range n).image (fun i => 2 * i + 1) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, ⟨i, by omega⟩⟩
  rw [he, card_image_of_injective _ (by intro a b h; dsimp at h; omega), card_range]
  omega

/-- LEAF. Unit U-1537. `r''_{2k}(N) > 0` gives a representation of `N` as two primes plus `2k`
powers of 2 with exponents `≥ 1`, the conclusion of Theorem 1 p. 1 from (6.9) to (6.11) p. 12. The
conclusion is the body of `LeanLab.Linnik.LinnikExact (2 * k) N`. -/
theorem exists_of_pos {N1 N k L : ℕ} (h : 0 < rK'' N1 N k L) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ∃ ν : Fin (2 * k) → ℕ, (∀ i, 1 ≤ ν i) ∧
      N = p + q + ∑ i, 2 ^ ν i := by
  have choose {ι : Type} (s : Finset ι) (f : ι → ℝ) (hh : 0 < ∑ i ∈ s, f i) :
      ∃ i ∈ s, 0 < f i := by
    by_contra! hn
    have := sum_nonpos hn
    linarith
  unfold rK'' at h
  obtain ⟨p, hp, hpv⟩ := choose _ _ h
  obtain ⟨q, hq, hqv⟩ := choose _ _ hpv
  obtain ⟨ν, _, hν⟩ := choose _ _ hqv
  split_ifs at hν with he
  · refine ⟨p, q, (mem_filter.mp hp).2, (mem_filter.mp hq).2,
      (fun i => (ν i : ℕ) + 1), ?_, ?_⟩
    · intro i
      exact Nat.succ_le_succ (Nat.zero_le _)
    · exact he.symm
  · simp at hν

/-! ### Leaves: the exceptional classes in (4.5) and (6.3) -/

/-- LEAF. Unit U-1537. The union over `i = 1, ..., M` in (4.5) p. 9 and (6.3) p. 11:
`∑_{x : ∃ r ∈ rs, P r x} f(x) ≤ ∑_{r ∈ rs} ∑_{x : P r x} f(x)` for `f ≥ 0`. -/
theorem union_bound {ι : Type*} (s : Finset ι) (rs : Finset ℕ) (P : ℕ → ι → Prop)
    [∀ r x, Decidable (P r x)] (f : ι → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.filter (fun x => ∃ r ∈ rs, P r x), f x ≤ ∑ r ∈ rs, ∑ x ∈ s.filter (P r), f x := by
  classical
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro x hx
  split_ifs with h
  · obtain ⟨r, hr, hp⟩ := h
    exact (by simpa [hp] using (single_le_sum (f := fun r => if P r x then f x else 0)
      (fun r _ => by split_ifs <;> first | exact hf x | exact le_rfl) hr))
  · exact sum_nonneg fun r _ => by split_ifs <;> first | exact hf x | exact le_rfl

/-- LEAF. Unit U-1537. The sentence after (4.5) p. 9: fixing `ν₂` and putting `m = 2^{ν₂}`, the
bad `ν₁ < ν₂` of one class `H_i` contribute at most the Lemma 1 bound `T`, so over all `ν₂ ≤ L`
at most `L T`. -/
theorem bad_reindex_1 {L r C : ℕ} {T : ℝ}
    (hT : ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
      ∑ ν ∈ (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0 ∧ (r : ℤ) ∣ C * (m - 2 ^ ν)),
        sfac (m - 2 ^ ν) ≤ T) :
    ∑ x ∈ (star L).filter (fun x => (r : ℤ) ∣ C * hdiff x), sfac (hdiff x) ≤ L * T := by
  unfold star hdiff
  rw [filter_filter, sum_filter, sum_product, sum_comm]
  calc
    _ ≤ ∑ b ∈ Icc 1 L, T := by
      apply sum_le_sum
      intro b hb
      have hbL := (mem_Icc.mp hb).2
      have hbm : |(2 : ℤ) ^ b| ≤ 2 ^ (2 * L) := by
        rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc
        _ ≤ ∑ a ∈ (Icc 1 L).filter (fun a => (2 : ℤ) ^ b - 2 ^ a ≠ 0 ∧
            (r : ℤ) ∣ C * ((2 : ℤ) ^ b - 2 ^ a)), sfac ((2 : ℤ) ^ b - 2 ^ a) := by
          rw [sum_filter]
          apply sum_le_sum
          intro a ha
          by_cases hab : a < b ∧ (r : ℤ) ∣ C * ((2 : ℤ) ^ b - 2 ^ a)
          · have hp : (2 : ℤ) ^ a < 2 ^ b := pow_lt_pow_right₀ (by norm_num) hab.1
            have hn : (2 : ℤ) ^ b - 2 ^ a ≠ 0 := by omega
            simp only [if_pos hab, if_pos (show (2 : ℤ) ^ b - 2 ^ a ≠ 0 ∧ (r : ℤ) ∣ C * ((2 : ℤ) ^ b - 2 ^ a) from ⟨hn, hab.2⟩)]
            exact le_rfl
          · rw [if_neg hab]
            split_ifs <;> first | exact sfac_nonneg _ | exact le_rfl
        _ ≤ T := hT _ hbm
    _ = _ := by simp

/-- LEAF. Unit U-1537. The last sum of (6.3) p. 11: fixing `ν₁, ..., ν_k, μ₁, ..., μ_{k-1}` and
putting `m = 2^{ν₁} + ... - 2^{μ_{k-1}}`, `|m| ≤ k 2^L ≤ 2^{2L}`, the bad `μ_k` of one class
contribute at most the Lemma 1 bound `T`, so in all at most `L^{2k-1} T`. -/
theorem bad_reindex_k {k L r C : ℕ} {T : ℝ} (hk : 1 ≤ k) (hL : 2 * k ≤ 2 ^ L)
    (hT : ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
      ∑ ν ∈ (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0 ∧ (r : ℤ) ∣ C * (m - 2 ^ ν)),
        sfac (m - 2 ^ ν) ≤ T) :
    ∑ x ∈ univ.filter (fun x : pairs k L => difc x ≠ 0 ∧ (r : ℤ) ∣ C * difc x), sfac (difc x) ≤
      (L : ℝ) ^ (2 * k - 1) * T := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hb {n : ℕ} (ν : Fin n → Fin L) : svv ν ≤ n * 2 ^ L := by
    unfold svv
    calc
      ∑ i, 2 ^ ((ν i : ℕ) + 1) ≤ ∑ _i : Fin n, 2 ^ L :=
        sum_le_sum fun i _ => Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = _ := by simp
  have hbig : (j + 1) * 2 ^ L ≤ 2 ^ (2 * L) := by
    calc
      _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [← pow_add, two_mul]
  have hs (ν : Fin (j + 1) → Fin L) (μ : Fin j → Fin L) :
      (∑ a : Fin L, if difc (ν, Fin.cons a μ) ≠ 0 ∧ (r : ℤ) ∣ C * difc (ν, Fin.cons a μ)
        then sfac (difc (ν, Fin.cons a μ)) else 0) ≤ T := by
    let m : ℤ := (svv ν : ℤ) - svv μ
    have hm : |m| ≤ 2 ^ (2 * L) := by
      have hn : (svv ν : ℤ) ≤ (2 : ℤ) ^ (2 * L) := by exact_mod_cast (hb ν).trans hbig
      have hμ : (svv μ : ℤ) ≤ (2 : ℤ) ^ (2 * L) := by
        exact_mod_cast (hb μ).trans ((Nat.mul_le_mul_right (2 ^ L) (by omega : j ≤ j + 1)).trans hbig)
      dsimp [m]
      rw [abs_le]
      constructor <;> omega
    have hd (a : Fin L) : difc (ν, Fin.cons a μ) = m - 2 ^ ((a : ℕ) + 1) := by
      have hh : svv (Fin.cons a μ) = 2 ^ ((a : ℕ) + 1) + svv μ := by
        simp [svv, Fin.sum_univ_succ]
      simp only [difc, hh, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, m]
      ring
    simp_rw [hd]
    have hi : Icc 1 L = (range L).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext x
      simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega
    have ht := hT m hm
    rw [sum_filter, hi, sum_map] at ht
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => if m - 2 ^ (a + 1) ≠ 0 ∧
      (r : ℤ) ∣ C * (m - 2 ^ (a + 1)) then sfac (m - 2 ^ (a + 1)) else 0) L]
    exact ht
  rw [sum_filter, Fintype.sum_prod_type]
  calc
    _ = ∑ ν : Fin (j + 1) → Fin L, ∑ μ : Fin j → Fin L, ∑ a : Fin L,
        if difc (ν, Fin.cons a μ) ≠ 0 ∧ (r : ℤ) ∣ C * difc (ν, Fin.cons a μ)
          then sfac (difc (ν, Fin.cons a μ)) else 0 := by
      apply sum_congr rfl
      intro ν _
      rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => Fin L)).sum_comp, Fintype.sum_prod_type, sum_comm]
      rfl
    _ ≤ ∑ _ν : Fin (j + 1) → Fin L, ∑ _μ : Fin j → Fin L, T :=
      sum_le_sum fun ν _ => sum_le_sum fun μ _ => hs ν μ
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

/-! ### Assemblies: Lemma 5, p. 8 -/

/-- **(4.4) p. 9. CONDITIONAL ON `parseval_k`, `split3`, `major_expand`, `pair_k1`.**
`S₂(N) = S(N) - 2 ∑* R₁(2^{ν₂} - 2^{ν₁}) - L R₁(0)` with `S(N) = ∑_n r'_1(n)²`, (4.1) p. 8. -/
theorem identity44 (N1 N L : ℕ) (P Q : ℝ) :
    S2 N1 N L P Q = ∑ n ∈ range (N + 1 * 2 ^ (L + 1) + 1), (rk' N1 N 1 L n) ^ 2
      - 2 * ∑ x ∈ star L, (R1 N1 N P Q (hdiff x)).re - L * (R1 N1 N P Q 0).re := by
  have h1 := parseval_k N1 N 1 L Q
  have h2 := split3 N1 N 1 L P Q ∅ MeasurableSet.empty
  have h3 := major_expand N1 N 1 L P Q
  have h5 := pair_k1 N1 N L P Q
  simp only [Set.inter_empty, Measure.restrict_empty, integral_zero_measure, add_zero,
    Set.diff_empty, pow_one] at h1 h2
  have hmaj : ∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α * Gsum L α‖ ^ 2 =
      ∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α‖ ^ 2 * ‖Gsum L α‖ ^ (2 * 1) := by
    congr 1
    funext α
    simp only [norm_mul, mul_pow, mul_one]
  unfold S2
  linarith

/-- **Lemma 5, (4.7) p. 9, at fixed `N`. CONDITIONAL ON the leaves of `identity44` and on
`R1_zero_re_nonneg`.** Inputs, as hypotheses: `hL4`, Lemma 4 p. 8, part I Lemma 10,
`S(N) ≤ 2 C₂ N L²`; `hgood`, `hall`, Corollary 1 p. 5 at `h = 2^{ν₂} - 2^{ν₁}`: the lower bound
`(1 - ε) 𝔖(h) N ≤ R₁(h)` off the exceptional classes and `R₁(h) ≥ -B 𝔖(h) N` always; `h46`,
display (4.6) p. 9, part I (8.8) to (8.14), with `CR = C₀ R₀`; `hbad`, the exceptional classes,
bounded by `lemma5_bad_bound`. Conclusion: `S₂(N) ≤ 2NL²(C₂ - C₀R₀(1 - ε - δ)) + 2(1 + B) N β`;
with `C₂ = C₀R₀C* + log 2/2` this is (4.7), `C₀R₀(C* - 1) + log 2/2 + O(ε)`. -/
theorem lemma5_of_leaves (N1 N L : ℕ) (P Q : ℝ) (c0 ε δ B β C2 CR : ℝ)
    (bad : ℕ × ℕ → Prop) [DecidablePred bad]
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hCR : 0 ≤ CR) (hc0 : 0 ≤ c0)
    (hL4 : ∑ n ∈ range (N + 1 * 2 ^ (L + 1) + 1), (rk' N1 N 1 L n) ^ 2 ≤ 2 * C2 * N * L ^ 2)
    (hgood : ∀ x ∈ star L, ¬ bad x →
      (1 - ε) * sing c0 (hdiff x) * N ≤ (R1 N1 N P Q (hdiff x)).re)
    (hall : ∀ x ∈ star L, -(B * sing c0 (hdiff x) * N) ≤ (R1 N1 N P Q (hdiff x)).re)
    (h46 : 2 * CR * L ^ 2 * (1 - δ) ≤ 2 * ∑ x ∈ star L, sing c0 (hdiff x))
    (hbad : ∑ x ∈ (star L).filter bad, sing c0 (hdiff x) ≤ β) :
    S2 N1 N L P Q ≤ 2 * N * L ^ 2 * (C2 - CR * (1 - ε - δ)) + 2 * (1 + B) * N * β := by
  rw [identity44]
  have hR0 := R1_zero_re_nonneg N1 N P Q
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hpt : ∀ x ∈ star L, (1 - ε) * sing c0 (hdiff x) * N -
      (if bad x then (1 - ε + B) * sing c0 (hdiff x) * N else 0) ≤
      (R1 N1 N P Q (hdiff x)).re := by
    intro x hx
    split_ifs with hb
    · have := hall x hx
      linarith
    · have := hgood x hx hb
      linarith
  have hsum := sum_le_sum hpt
  rw [sum_sub_distrib] at hsum
  have e1 : ∑ x ∈ star L, (1 - ε) * sing c0 (hdiff x) * N =
      (1 - ε) * N * ∑ x ∈ star L, sing c0 (hdiff x) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  have e2 : ∑ x ∈ star L, (if bad x then (1 - ε + B) * sing c0 (hdiff x) * N else 0) =
      (1 - ε + B) * N * ∑ x ∈ (star L).filter bad, sing c0 (hdiff x) := by
    rw [mul_sum, sum_filter]
    apply sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [e1, e2] at hsum
  set Sg := ∑ x ∈ star L, sing c0 (hdiff x) with hSg
  set Sb := ∑ x ∈ (star L).filter bad, sing c0 (hdiff x) with hSb
  have hSb0 : 0 ≤ Sb := sum_nonneg fun x _ => sing_nonneg hc0 _
  have h1e : 0 ≤ 1 - ε := by linarith
  have h_a : (1 - ε) * N * (CR * L ^ 2 * (1 - δ)) ≤ (1 - ε) * N * Sg :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg h1e hNn)
  have h_b : (1 - ε) * N * (CR * L ^ 2 * (1 - δ)) - N * CR * L ^ 2 * (1 - ε - δ) =
      N * CR * L ^ 2 * (ε * δ) := by ring
  have h_b' : 0 ≤ N * CR * L ^ 2 * (ε * δ) := by positivity
  have h_c : (1 - ε + B) * N * Sb ≤ (1 + B) * N * β := by
    calc (1 - ε + B) * N * Sb ≤ (1 - ε + B) * N * β :=
          mul_le_mul_of_nonneg_left hbad (mul_nonneg (by linarith) hNn)
      _ ≤ (1 + B) * N * β :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hNn)
            (hSb0.trans hbad)
  have h_d : 0 ≤ (L : ℝ) * (R1 N1 N P Q 0).re := mul_nonneg hLn hR0
  nlinarith

/-- **The exceptional classes in Lemma 5, the error term of (4.5) p. 9. CONDITIONAL ON
`Decomp1537a.lemma1_class`, `union_bound`, `bad_reindex_1`.** For every `η > 0` there are
`T, L₀` such that for `L ≥ L₀`, constants `C ≥ 1`, `0 ≤ c₀ ≤ 1`, and moduli `r ∈ rs` with odd
squarefree part `≥ T C`, the `h = 2^{ν₂} - 2^{ν₁}` in some class `H_r = {h : r | C h}` have
`∑* 𝔖(h) ≤ |rs| · 2 L (η L)`, which is `O(εL²)` once `η` is chosen against `M = |rs|`. -/
theorem lemma5_bad_bound {η : ℝ} (hη : 0 < η) :
    ∃ T L0 : ℕ, ∀ L : ℕ, L0 ≤ L → ∀ (rs : Finset ℕ) (C : ℕ) (c0 : ℝ), 0 < C → 0 ≤ c0 →
      c0 ≤ 1 → (∀ r ∈ rs, 0 < r ∧ T * C ≤ oddSqf r) →
      ∑ x ∈ (star L).filter (fun x => ∃ r ∈ rs, (r : ℤ) ∣ C * hdiff x), sing c0 (hdiff x) ≤
        rs.card * (2 * (L * (η * L))) := by
  obtain ⟨T, L0, h1⟩ := lemma1_class hη
  refine ⟨T, L0, fun L hL rs C c0 hC hc0 hc1 hrs => ?_⟩
  calc ∑ x ∈ (star L).filter (fun x => ∃ r ∈ rs, (r : ℤ) ∣ C * hdiff x), sing c0 (hdiff x)
      ≤ ∑ r ∈ rs, ∑ x ∈ (star L).filter (fun x => (r : ℤ) ∣ C * hdiff x), sing c0 (hdiff x) :=
        union_bound (star L) rs (fun r x => (r : ℤ) ∣ C * hdiff x) _
          (fun x => sing_nonneg hc0 _)
    _ ≤ ∑ r ∈ rs, (2 * (L * (η * L)) : ℝ) := by
        apply sum_le_sum
        intro r hr
        have hT := h1 L hL r C (hrs r hr).1 hC (hrs r hr).2
        have hb := bad_reindex_1 hT
        calc ∑ x ∈ (star L).filter (fun x => (r : ℤ) ∣ C * hdiff x), sing c0 (hdiff x)
            ≤ ∑ x ∈ (star L).filter (fun x => (r : ℤ) ∣ C * hdiff x), 2 * sfac (hdiff x) :=
              sum_le_sum fun x _ => sing_le hc0 hc1 _
          _ = 2 * ∑ x ∈ (star L).filter (fun x => (r : ℤ) ∣ C * hdiff x), sfac (hdiff x) := by
              rw [mul_sum]
          _ ≤ 2 * (L * (η * L)) := by linarith
    _ = rs.card * (2 * (L * (η * L))) := by rw [sum_const, nsmul_eq_mul]

/-! ### Assemblies: Lemma 9, p. 10 -/

/-- **The good and bad split of a weighted sum, as in (4.5) p. 9 and (6.3) p. 11. Proved.**
If `x_i ≤ a y_i` off the bad set, `x_i ≤ b y_i` always, `w_i ≥ 0` and `a y_i ≥ 0`, then
`∑ w x ≤ a ∑ w y + b ∑_{bad} w y`. -/
theorem weighted_split {ι : Type*} (s : Finset ι) (bad : ι → Prop) [DecidablePred bad]
    (w x y : ι → ℝ) (a b : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hy : ∀ i ∈ s, 0 ≤ a * y i)
    (hgood : ∀ i ∈ s, ¬ bad i → x i ≤ a * y i) (hall : ∀ i ∈ s, x i ≤ b * y i) :
    ∑ i ∈ s, w i * x i ≤ a * ∑ i ∈ s, w i * y i + b * ∑ i ∈ s.filter bad, w i * y i := by
  have hpt : ∀ i ∈ s, w i * x i ≤ a * (w i * y i) + (if bad i then b * (w i * y i) else 0) := by
    intro i hi
    have hwi := hw i hi
    split_ifs with hb
    · have h1 := mul_le_mul_of_nonneg_left (hall i hi) hwi
      have h2 := mul_nonneg hwi (hy i hi)
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left (hgood i hi hb) hwi
      nlinarith
  calc ∑ i ∈ s, w i * x i
      ≤ ∑ i ∈ s, (a * (w i * y i) + (if bad i then b * (w i * y i) else 0)) := sum_le_sum hpt
    _ = a * ∑ i ∈ s, w i * y i + b * ∑ i ∈ s.filter bad, w i * y i := by
        rw [sum_add_distrib, ← mul_sum]
        congr 1
        rw [sum_filter, mul_sum]
        apply sum_congr rfl
        intro i _
        split_ifs <;> ring

/-- **Lemma 9, (6.1) p. 10, at fixed `N`, in the shape (6.2) to (6.5) p. 11. CONDITIONAL ON
`parseval_k`, `split3`, `major_expand`, `R1_zero_re_le`, `sum_log_sq_le`, `R1_zero_re_nonneg`,
`minor_compare`, `E_part`.** Inputs, as hypotheses: `hrkk0`, Lemma 8 p. 10, part I Lemma 12,
`r_{k,k}(0) ≤ 2L^{2k-2}`; `hgood`, `hall`, Corollary 1 p. 5, upper bounds
`R₁(m) ≤ (1 + ε) N 𝔖(m)` off the exceptional classes and `R₁(m) ≤ B N 𝔖(m)` always, Theorem 2
p. 4; `hW`, Lemma 7 p. 10, Khalfalah-Pintz, `∑_{m ≠ 0} r_{k,k}(m) 𝔖(m) ≤ W ≈ 2L^{2k}(1 + A(k))`;
`hβ`, the classes, bounded by `lemma9_bad_bound`; `hS`, Lemma 2 p. 8, Vinogradov, `|S| ≤ Ssup`
on `C(𝔐)`; `hG`, Lemma 6 p. 10, part I Corollary 2, `|G| ≤ c₁ L` off `E*`, `|E*| ≤ eE`;
`hS2`, Lemma 5. Conclusion: the sum of the three bounds (6.3), (6.5), (6.4). -/
theorem lemma9_of_leaves (N1 N k L : ℕ) (P Q : ℝ) (hk : 1 ≤ k)
    (c0 ε B W β eE Ssup c1 S2b : ℝ) (bad : ℤ → Prop) [DecidablePred bad] (E : Set ℝ)
    (hε : 0 ≤ 1 + ε) (hB : 0 ≤ B) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hrkk0 : (rkk k L 0 : ℝ) ≤ 2 * (L : ℝ) ^ (2 * k - 2))
    (hgood : ∀ m ∈ (mset k L).filter (fun m => m ≠ 0), ¬ bad m →
      (R1 N1 N P Q m).re ≤ (1 + ε) * N * sing c0 m)
    (hall : ∀ m ∈ (mset k L).filter (fun m => m ≠ 0), (R1 N1 N P Q m).re ≤ B * N * sing c0 m)
    (hW : ∑ m ∈ (mset k L).filter (fun m => m ≠ 0), (rkk k L m : ℝ) * sing c0 m ≤ W)
    (hβ : ∑ m ∈ ((mset k L).filter (fun m => m ≠ 0)).filter bad, (rkk k L m : ℝ) * sing c0 m ≤ β)
    (hE : MeasurableSet E) (hEf : volume E ≠ ⊤) (hEv : (volume E).toReal ≤ eE)
    (hS : ∀ α ∈ Ufull Q \ majorArcs P Q, ‖Ssum N1 N α‖ ≤ Ssup)
    (hG : ∀ α ∈ (Ufull Q \ majorArcs P Q) \ E, ‖Gsum L α‖ ≤ c1 * L)
    (hS2 : S2 N1 N L P Q ≤ S2b) :
    ∑ n ∈ range (N + k * 2 ^ (L + 1) + 1), (rk' N1 N k L n) ^ 2 ≤
      2 * (L : ℝ) ^ (2 * k - 2) * (2 * N * Real.log N) + ((1 + ε) * N * W + B * N * β)
      + eE * Ssup ^ 2 * (L : ℝ) ^ (2 * k) + (c1 * L) ^ (2 * k - 2) * S2b := by
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  rw [← parseval_k N1 N k L Q, split3 N1 N k L P Q E hE]
  -- the major arcs, (6.3)
  have hmaj : ∫ α in majorArcs P Q ∩ Ufull Q, ‖Ssum N1 N α * Gsum L α ^ k‖ ^ 2 =
      ∑ m ∈ mset k L, (rkk k L m : ℝ) * (R1 N1 N P Q m).re := by
    rw [← major_expand N1 N k L P Q]
    congr 1
    funext α
    rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm k 2]
  have hsplit0 : ∑ m ∈ mset k L, (rkk k L m : ℝ) * (R1 N1 N P Q m).re =
      (rkk k L 0 : ℝ) * (R1 N1 N P Q 0).re +
        ∑ m ∈ (mset k L).filter (fun m => m ≠ 0), (rkk k L m : ℝ) * (R1 N1 N P Q m).re := by
    rw [← sum_filter_add_sum_filter_not (mset k L) (fun m => m = 0)]
    congr 1
    have h0 : (0 : ℤ) ∈ mset k L := by
      unfold mset Bk
      simp
    rw [filter_eq' (mset k L) 0, if_pos h0, sum_singleton]
  have hR0 := R1_zero_re_nonneg N1 N P Q
  have hR0le : (R1 N1 N P Q 0).re ≤ 2 * N * Real.log N :=
    (R1_zero_re_le N1 N P Q).trans (sum_log_sq_le N1 N)
  have hzero : (rkk k L 0 : ℝ) * (R1 N1 N P Q 0).re ≤
      2 * (L : ℝ) ^ (2 * k - 2) * (2 * N * Real.log N) :=
    mul_le_mul hrkk0 hR0le hR0 (by positivity)
  have hws := weighted_split ((mset k L).filter (fun m => m ≠ 0)) bad
    (fun m => (rkk k L m : ℝ)) (fun m => (R1 N1 N P Q m).re) (fun m => sing c0 m)
    ((1 + ε) * N) (B * N) (fun m _ => Nat.cast_nonneg _)
    (fun m _ => mul_nonneg (mul_nonneg hε hNn) (sing_nonneg hc0 m)) hgood hall
  have hW' : (1 + ε) * N * ∑ m ∈ (mset k L).filter (fun m => m ≠ 0), (rkk k L m : ℝ) * sing c0 m
      ≤ (1 + ε) * N * W := mul_le_mul_of_nonneg_left hW (mul_nonneg hε hNn)
  have hβ' : B * N * ∑ m ∈ ((mset k L).filter (fun m => m ≠ 0)).filter bad,
      (rkk k L m : ℝ) * sing c0 m ≤ B * N * β := mul_le_mul_of_nonneg_left hβ (mul_nonneg hB hNn)
  -- the exceptional set E*, (6.5)
  have hEp := E_part N1 N k L P Q hE hEf hS
  have hEp' : (volume E).toReal * Ssup ^ 2 * (L : ℝ) ^ (2 * k) ≤
      eE * Ssup ^ 2 * (L : ℝ) ^ (2 * k) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEv (sq_nonneg _)) (by positivity)
  -- the minor arcs off E*, (6.4)
  have hmin := minor_compare N1 N k L P Q hk ((minor_measurable P Q).diff hE)
    Set.diff_subset hc1 hG
  have hmin' : (c1 * L) ^ (2 * k - 2) * S2 N1 N L P Q ≤ (c1 * L) ^ (2 * k - 2) * S2b :=
    mul_le_mul_of_nonneg_left hS2 (by positivity)
  rw [hmaj, hsplit0]
  linarith

/-- **The exceptional classes in Lemma 9, the last error term of (6.3) p. 11. CONDITIONAL ON
`Decomp1537a.lemma1_class`, `rkk_sum_eq`, `union_bound`, `bad_reindex_k`.** For every `η > 0`
and `k ≥ 1` there are `T, L₀` such that for `L ≥ L₀` with `2k ≤ 2^L`, `C ≥ 1`, `0 ≤ c₀ ≤ 1` and
moduli `r ∈ rs` with odd squarefree part `≥ T C`:
`∑_{m ≠ 0, m ∈ ∪ H_r} r_{k,k}(m) 𝔖(m) ≤ |rs| · 2 L^{2k-1} (η L)`, which is `O(ε L^{2k})`. -/
theorem lemma9_bad_bound {η : ℝ} (hη : 0 < η) (k : ℕ) (hk : 1 ≤ k) :
    ∃ T L0 : ℕ, ∀ L : ℕ, L0 ≤ L → 2 * k ≤ 2 ^ L → ∀ (rs : Finset ℕ) (C : ℕ) (c0 : ℝ),
      0 < C → 0 ≤ c0 → c0 ≤ 1 → (∀ r ∈ rs, 0 < r ∧ T * C ≤ oddSqf r) →
      ∑ m ∈ ((mset k L).filter (fun m => m ≠ 0)).filter (fun m => ∃ r ∈ rs, (r : ℤ) ∣ C * m),
        (rkk k L m : ℝ) * sing c0 m ≤ rs.card * (2 * ((L : ℝ) ^ (2 * k - 1) * (η * L))) := by
  obtain ⟨T, L0, h1⟩ := lemma1_class hη
  refine ⟨T, L0, fun L hL hkL rs C c0 hC hc0 hc1 hrs => ?_⟩
  have e1 : ∑ m ∈ ((mset k L).filter (fun m => m ≠ 0)).filter
      (fun m => ∃ r ∈ rs, (r : ℤ) ∣ C * m), (rkk k L m : ℝ) * sing c0 m =
      ∑ m ∈ mset k L, (rkk k L m : ℝ) *
        (if m ≠ 0 ∧ (∃ r ∈ rs, (r : ℤ) ∣ C * m) then sing c0 m else 0) := by
    rw [filter_filter, sum_filter]
    apply sum_congr rfl
    intro m _
    split_ifs <;> simp
  have e2 : ∑ x : pairs k L,
      (if difc x ≠ 0 ∧ (∃ r ∈ rs, (r : ℤ) ∣ C * difc x) then sing c0 (difc x) else 0) =
      ∑ x ∈ (univ.filter (fun x : pairs k L => difc x ≠ 0)).filter
        (fun x => ∃ r ∈ rs, (r : ℤ) ∣ C * difc x), sing c0 (difc x) := by
    rw [filter_filter, sum_filter]
  calc _ = _ := e1
    _ = _ := rkk_sum_eq k L
          (fun m => if m ≠ 0 ∧ (∃ r ∈ rs, (r : ℤ) ∣ C * m) then sing c0 m else 0)
    _ = _ := e2
    _ ≤ ∑ r ∈ rs, ∑ x ∈ (univ.filter (fun x : pairs k L => difc x ≠ 0)).filter
          (fun x => (r : ℤ) ∣ C * difc x), sing c0 (difc x) :=
        union_bound _ rs (fun r x => (r : ℤ) ∣ C * difc x) _ (fun x => sing_nonneg hc0 _)
    _ ≤ ∑ r ∈ rs, (2 * ((L : ℝ) ^ (2 * k - 1) * (η * L)) : ℝ) := by
        apply sum_le_sum
        intro r hr
        have hT := h1 L hL r C (hrs r hr).1 hC (hrs r hr).2
        have hb := bad_reindex_k hk hkL hT
        rw [filter_filter]
        calc ∑ x ∈ univ.filter (fun x : pairs k L => difc x ≠ 0 ∧ (r : ℤ) ∣ C * difc x),
              sing c0 (difc x)
            ≤ ∑ x ∈ univ.filter (fun x : pairs k L => difc x ≠ 0 ∧ (r : ℤ) ∣ C * difc x),
              2 * sfac (difc x) := sum_le_sum fun x _ => sing_le hc0 hc1 _
          _ = 2 * ∑ x ∈ univ.filter (fun x : pairs k L => difc x ≠ 0 ∧ (r : ℤ) ∣ C * difc x),
              sfac (difc x) := by rw [mul_sum]
          _ ≤ 2 * ((L : ℝ) ^ (2 * k - 1) * (η * L)) := by linarith
    _ = rs.card * (2 * ((L : ℝ) ^ (2 * k - 1) * (η * L))) := by rw [sum_const, nsmul_eq_mul]

/-! ### Assemblies: the end of the proof, (6.6) to (6.11), p. 12 -/

/-- **(6.9) and (6.10) p. 12 at fixed even `N`. CONDITIONAL ON `convolution`, `rk'_even`,
`odd_count`.** If `∑_{n ≤ N} r'_k(n)² ≤ 2NL^{2k}(1 + C + δ)`, Lemma 9, and
`|∑_{n ≤ N} r'_k(n) - N L^k| ≤ δ N L^k`, the prime number theorem (6.6), then
`r''_{2k}(N) ≥ 2NL^{2k}(1 - C - 5δ)`. The paper's route: `s_k(n) = r'_k(n) - 2L^k` on odd `n`,
(6.7), and Cauchy's inequality (6.10). -/
theorem final_positivity (N1 N k L : ℕ) (hN : Even N) (hN1 : 2 ≤ N1) (Cc δ : ℝ)
    (hsq : ∑ n ∈ range (N + 1), (rk' N1 N k L n) ^ 2 ≤ 2 * N * (L : ℝ) ^ (2 * k) * (1 + Cc + δ))
    (hsum : |∑ n ∈ range (N + 1), rk' N1 N k L n - N * (L : ℝ) ^ k| ≤ δ * N * (L : ℝ) ^ k) :
    2 * N * (L : ℝ) ^ (2 * k) * (1 - Cc - 5 * δ) ≤ rK'' N1 N k L := by
  rw [convolution]
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = rk' N1 N k L := ⟨_, rfl⟩
  rw [← ha] at hsq hsum ⊢
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 2 * (L : ℝ) ^ k := ⟨_, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o : ℕ → ℝ, o = fun n => if Odd n then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun n => a n ^ 2 - 2 * lam * a n + lam ^ 2 * o n :=
    ⟨_, rfl⟩
  have hae : ∀ n, a n * o n = a n := by
    intro n
    simp only [ho]
    split_ifs with hn
    · ring
    · have : a n = 0 := by
        rw [ha]; exact rk'_even N1 N k L hN1 (Nat.not_odd_iff_even.mp hn)
      rw [this]; ring
  have hpar : ∀ m ∈ range (N + 1), o (N - m) = o m := by
    intro m hm
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hiff : Odd (N - m) ↔ Odd m := by
      rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, Nat.even_sub hmN]
      tauto
    simp only [ho]
    by_cases h : Odd m
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
  -- pointwise: `a_m a_{N-m} ≥ -(f m + f (N - m))/2 + lam a_{N-m} + lam a_m - lam² o_m`,
  -- which is `s_m s_{N-m} ≥ -(s_m² + s_{N-m}²)/2` for `s = a - lam o`, the Cauchy step (6.10)
  have hpt : ∀ m ∈ range (N + 1), -(f m + f (N - m)) / 2 + lam * a (N - m) + lam * a m
      - lam ^ 2 * o m ≤ a m * a (N - m) := by
    intro m hm
    have hp := hpar m hm
    simp only [hf]
    rw [hp]
    by_cases h : Odd m
    · have h1 : o m = 1 := by simp only [ho, if_pos h]
      rw [h1]
      nlinarith [sq_nonneg (a m + a (N - m) - 2 * lam)]
    · have h0 : o m = 0 := by simp only [ho, if_neg h]
      have hm0 : a m = 0 := by
        have := hae m
        rw [h0, mul_zero] at this
        exact this.symm
      have hNm0 : a (N - m) = 0 := by
        have := hae (N - m)
        rw [hp, h0, mul_zero] at this
        exact this.symm
      rw [h0, hm0, hNm0]
      norm_num
  have hsum1 := sum_le_sum hpt
  have hrefl : ∀ g : ℕ → ℝ, ∑ m ∈ range (N + 1), g (N - m) = ∑ m ∈ range (N + 1), g m := by
    intro g
    have := sum_range_reflect g (N + 1)
    simpa [Nat.add_sub_cancel] using this
  have hfsum : ∑ m ∈ range (N + 1), f m = ∑ m ∈ range (N + 1), a m ^ 2
      - 2 * lam * ∑ m ∈ range (N + 1), a m + lam ^ 2 * ∑ m ∈ range (N + 1), o m := by
    simp only [hf, sum_add_distrib, sum_sub_distrib, mul_sum]
  have hosum : ∑ m ∈ range (N + 1), o m = (N : ℝ) / 2 := by
    simp only [ho]
    rw [sum_boole, odd_count hN]
    have h2 : 2 ∣ N := even_iff_two_dvd.mp hN
    rw [Nat.cast_div h2 (by norm_num)]
    norm_num
  have hexp : ∀ m, -(f m + f (N - m)) / 2 + lam * a (N - m) + lam * a m - lam ^ 2 * o m =
      (-(1 / 2 : ℝ)) * f m + (-(1 / 2 : ℝ)) * f (N - m) + lam * a (N - m) + lam * a m
        + (-lam ^ 2) * o m := by
    intro m; ring
  have hlhs : ∑ m ∈ range (N + 1), (-(f m + f (N - m)) / 2 + lam * a (N - m) + lam * a m
      - lam ^ 2 * o m) = -(∑ m ∈ range (N + 1), f m) + 2 * lam * ∑ m ∈ range (N + 1), a m
      - lam ^ 2 * ∑ m ∈ range (N + 1), o m := by
    simp only [hexp, sum_add_distrib, ← mul_sum]
    rw [hrefl f, hrefl a]
    ring
  rw [hlhs, hfsum, hosum, hlam] at hsum1
  have hsum' : (1 - δ) * (N * (L : ℝ) ^ k) ≤ ∑ n ∈ range (N + 1), a n := by
    have := (abs_le.mp hsum).1
    linarith
  have hLk : 0 ≤ (L : ℝ) ^ k := by positivity
  have hpow : (L : ℝ) ^ (2 * k) = (L : ℝ) ^ k * (L : ℝ) ^ k := by rw [two_mul, pow_add]
  have hfin : 8 * (L : ℝ) ^ k * ((1 - δ) * (N * (L : ℝ) ^ k)) ≤
      8 * (L : ℝ) ^ k * ∑ n ∈ range (N + 1), a n :=
    mul_le_mul_of_nonneg_left hsum' (by positivity)
  rw [hpow] at hsq ⊢
  nlinarith

/-- **Theorem 1 p. 1 at `K = 8`, the last step (6.11) p. 12, at fixed even `N`. CONDITIONAL ON
the leaves of `final_positivity`.** With `k = 4`, `c₁ = 0.789401`, `C₂' = 4.0826`,
`A(4) < 0.004`, (5.3) p. 10, and `δ ≤ 0.001` in the two inputs, `r''_8(N) > 0`. The numerical
step is the lab's `PR2020.c3_lt`, `C₃(4) < 0.992`. -/
theorem k4_positive (N1 N L : ℕ) (hN : Even N) (hN1 : 2 ≤ N1) (hNpos : 0 < N) (hL : 0 < L)
    (A δ : ℝ) (hA : A < 0.004) (hδ : δ ≤ 0.001)
    (hsq : ∑ n ∈ range (N + 1), (rk' N1 N 4 L n) ^ 2 ≤
      2 * N * (L : ℝ) ^ (2 * 4) * (1 + (A + 4.0826 * (0.789401 : ℝ) ^ 6) + δ))
    (hsum : |∑ n ∈ range (N + 1), rk' N1 N 4 L n - N * (L : ℝ) ^ 4| ≤ δ * N * (L : ℝ) ^ 4) :
    0 < rK'' N1 N 4 L := by
  have h := final_positivity N1 N 4 L hN hN1 (A + 4.0826 * (0.789401 : ℝ) ^ 6) δ hsq hsum
  have hc3 := LeanLab.Linnik.PR2020.c3_lt hA
  have hpos : 0 < 2 * (N : ℝ) * (L : ℝ) ^ (2 * 4) := by positivity
  have hm : 0 < 1 - (A + 4.0826 * (0.789401 : ℝ) ^ 6) - 5 * δ := by linarith
  exact lt_of_lt_of_le (mul_pos hpos hm) h

/-- **Two primes plus 8 powers of 2 at a fixed even `N`, CONDITIONAL ON the leaves of
`k4_positive` and `exists_of_pos` and on the two analytic inputs at that `N`.** The conclusion is
the body of `LeanLab.Linnik.LinnikExact 8 N`. -/
theorem k4_representation (N1 N L : ℕ) (hN : Even N) (hN1 : 2 ≤ N1) (hNpos : 0 < N) (hL : 0 < L)
    (A δ : ℝ) (hA : A < 0.004) (hδ : δ ≤ 0.001)
    (hsq : ∑ n ∈ range (N + 1), (rk' N1 N 4 L n) ^ 2 ≤
      2 * N * (L : ℝ) ^ (2 * 4) * (1 + (A + 4.0826 * (0.789401 : ℝ) ^ 6) + δ))
    (hsum : |∑ n ∈ range (N + 1), rk' N1 N 4 L n - N * (L : ℝ) ^ 4| ≤ δ * N * (L : ℝ) ^ 4) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ∃ ν : Fin (2 * 4) → ℕ, (∀ i, 1 ≤ ν i) ∧
      N = p + q + ∑ i, 2 ^ ν i :=
  exists_of_pos (k4_positive N1 N L hN hN1 hNpos hL A δ hA hδ hsq hsum)

/-- Finite bounds before the prime number theorem step. P0035 p.11 display 6.6. -/
theorem first_moment_bounds (N1 N k L : ℕ) :
    (L : ℝ) ^ k * (Chebyshev.theta ((N - k * 2 ^ L : ℕ) : ℝ) - Chebyshev.theta N1) ≤
      ∑ n ∈ range (N + 1), rk' N1 N k L n ∧
    (∑ n ∈ range (N + 1), rk' N1 N k L n) ≤ (L : ℝ) ^ k * Chebyshev.theta N := by
  have hsum : (∑ n ∈ range (N + 1), rk' N1 N k L n) =
      ∑ p ∈ primesIn N1 N, ∑ ν : Fin k → Fin L,
        if p + svv ν ≤ N then Real.log p else 0 := by
    unfold rk'
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    rw [sum_comm]
    apply sum_congr rfl
    intro ν _
    rw [sum_ite_eq]
    simp only [mem_range, Nat.lt_succ_iff]
  rw [hsum]
  have hnon : 0 ≤ ∑ p ∈ primesIn N1 N, ∑ ν : Fin k → Fin L,
      if p + svv ν ≤ N then Real.log p else 0 :=
    sum_nonneg fun p _ => sum_nonneg fun ν _ => by
      split_ifs <;> first | exact Real.log_natCast_nonneg p | exact le_rfl
  constructor
  · by_cases hMN : N1 ≤ N - k * 2 ^ L
    · rw [← LeanLab.Linnik.LiLiuDisplay37.sum_primesIn hMN, mul_sum]
      calc
        _ = ∑ p ∈ primesIn N1 (N - k * 2 ^ L), ∑ ν : Fin k → Fin L,
            if p + svv ν ≤ N then Real.log p else 0 := by
          apply sum_congr rfl
          intro p hp
          have hp' := mem_filter.mp hp
          have hp0 := hp'.2.pos
          have hpN := (mem_Ioc.mp hp'.1).2
          have hin (ν : Fin k → Fin L) : p + svv ν ≤ N := by
            have hh : svv ν ≤ k * 2 ^ L := LeanLab.Linnik.U1434Lemma21.sv_le ν
            omega
          simp only [if_pos (hin _), sum_const, card_univ, Fintype.card_fun,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [primesIn, mem_filter, mem_Ioc] at hp ⊢
            exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
          · intro p _ _
            apply sum_nonneg
            intro ν _
            split_ifs <;> first | exact Real.log_natCast_nonneg p | exact le_rfl
    · have ht : Chebyshev.theta ((N - k * 2 ^ L : ℕ) : ℝ) ≤ Chebyshev.theta N1 :=
        Chebyshev.theta_mono (by exact_mod_cast (show N - k * 2 ^ L ≤ N1 by omega))
      exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht)).trans hnon
  · calc
      _ ≤ ∑ p ∈ primesIn N1 N, ∑ _ν : Fin k → Fin L, Real.log p := by
        apply sum_le_sum
        intro p _
        apply sum_le_sum
        intro ν _
        split_ifs <;> first | exact le_rfl | exact Real.log_natCast_nonneg p
      _ = (L : ℝ) ^ k * ∑ p ∈ primesIn N1 N, Real.log p := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (LeanLab.Linnik.U1434Lemma21.sum_primes_le_theta N1 N) (by positivity)

open Filter
open LeanLab.Linnik.U1426ChainWire (Lfun)
open LeanLab.Linnik.U1429Display58 (N1f)
/-- The prime number theorem step with the paper cutoff. P0035 p.11 display 6.6. -/
theorem first_moment_estimate (k : ℕ) {κ : ℝ} (hκ : 0 < κ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ n ∈ range (N + 1), rk' (N1f κ N) N k (Lfun N) n) - N * (Lfun N : ℝ) ^ k| ≤
        δ * N * (Lfun N : ℝ) ^ k := by
  let ε := min δ 1
  have hε : 0 < ε := lt_min hδ zero_lt_one
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : ε ≤ δ := min_le_left _ _
  obtain ⟨C, hC⟩ := LeanLab.Linnik.LiLiuDisplay37PNT.theta_pnt (ε / 4) (by positivity)
  have hC0 : 0 ≤ C := by have hh := hC 0; simpa using hh
  have hsmall : ∀ᶠ N : ℕ in atTop, (k : ℝ) * 2 ^ Lfun N ≤ ε / 4 * N := by
    have hh := LeanLab.Linnik.U1434Lemma21.two_pow_small
      (η := ε / (4 * ((k : ℝ) + 1))) (by positivity)
    filter_upwards [hh] with N hN
    have hs := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ (k : ℝ) + 1)
    have he : ((k : ℝ) + 1) * (ε / (4 * ((k : ℝ) + 1)) * N) = ε / 4 * N := by
      field_simp
    rw [he] at hs
    have hp : 0 ≤ (2 : ℝ) ^ Lfun N := by positivity
    nlinarith
  filter_upwards [hsmall, LeanLab.Linnik.U1434Lemma21.N1_small hκ
    (η := ε / 8) (by positivity), tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 * C / ε)]
    with N h2 hMmax hCN
  have hCN' : 8 * C ≤ ε * N := by rwa [div_le_iff₀' hε] at hCN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  let K := N - k * 2 ^ Lfun N
  let M := N1f κ N
  have hM : (M : ℝ) ≤ ε / 8 * N := by
    have hm : (M : ℝ) ≤ (max M 2 : ℕ) := by exact_mod_cast Nat.le_max_left M 2
    exact hm.trans hMmax
  have hKle : k * 2 ^ Lfun N ≤ N := by
    have hh : ((k * 2 ^ Lfun N : ℕ) : ℝ) ≤ N := by push_cast; nlinarith
    exact_mod_cast hh
  have hKr : (K : ℝ) = N - (k : ℝ) * 2 ^ Lfun N := by
    dsimp [K]
    rw [Nat.cast_sub hKle]
    push_cast
    rfl
  have hθK := hC K
  have hθM := hC M
  have hθN := hC N
  rw [abs_le] at hθK hθM hθN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hKN : (1 - ε / 4) * N ≤ (K : ℝ) := by rw [hKr]; linarith
  have hq : (1 - ε / 2) * N ≤ (1 - ε / 4) * K := by
    have hh := mul_le_mul_of_nonneg_left hKN (by linarith : (0 : ℝ) ≤ 1 - ε / 4)
    nlinarith
  have hloθ : (1 - ε) * N ≤ Chebyshev.theta K - Chebyshev.theta M := by
    nlinarith
  have hupθ : Chebyshev.theta N ≤ (1 + ε) * N := by nlinarith
  obtain ⟨hlo, hup⟩ := first_moment_bounds (N1f κ N) N k (Lfun N)
  have hw : 0 ≤ (Lfun N : ℝ) ^ k := by positivity
  have hwl : (1 - ε) * (N * (Lfun N : ℝ) ^ k) ≤
      ∑ n ∈ range (N + 1), rk' (N1f κ N) N k (Lfun N) n := by
    calc
      _ = (Lfun N : ℝ) ^ k * ((1 - ε) * N) := by ring
      _ ≤ (Lfun N : ℝ) ^ k * (Chebyshev.theta K - Chebyshev.theta M) :=
        mul_le_mul_of_nonneg_left hloθ hw
      _ ≤ _ := hlo
  have hwu : (∑ n ∈ range (N + 1), rk' (N1f κ N) N k (Lfun N) n) ≤
      (1 + ε) * (N * (Lfun N : ℝ) ^ k) := by
    calc
      _ ≤ (Lfun N : ℝ) ^ k * Chebyshev.theta N := hup
      _ ≤ (Lfun N : ℝ) ^ k * ((1 + ε) * N) := mul_le_mul_of_nonneg_left hupθ hw
      _ = _ := by ring
  have heδ := mul_le_mul_of_nonneg_right hεδ (mul_nonneg hN0 hw)
  rw [abs_le]
  constructor <;> nlinarith

end LeanLab.Linnik.Decomp1537c
