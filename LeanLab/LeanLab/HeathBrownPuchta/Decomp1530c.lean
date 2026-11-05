/-
Heath-Brown and Puchta 2002, Integers represented as a sum of primes and powers of two,
arXiv math/0201299. Unit U-1530, run 20261026T0004Z-24325, type DECOMPOSE, file c of three.

Two open inputs of Assembly.lean, split into leaves:

1. Lemma 1's explicit exponents, Section 7, displays 43 to 45 and the choice `h = 16`:
   `E(0.863665) > 109/154` at `ξ = 1.181` and `E(0.722428) > 1/2` at `ξ = 0.905`, with
   `E = ξλ/log 2 - log F(ξ, h)/(h log 2)`. Display 44 says the supremum in `F` is attained at
   `β = 0`, `ρ = 1`, via the moments of display 45.
2. The circle method identity, Section 2: `R(N) = ∫₀¹ S(α)² T(α)^K e(-αN) dα` counts the
   representations `N = p + p' + 2^{ν₁} + ... + 2^{ν_K}`, so `Re R(N) > 0` gives one. In
   Assembly.lean this is the hypothesis `circle` of `theorem1_conditional` and
   `theorem2_conditional`.

Numerics, numpy double precision over all `2^16` residues: `F(1.181, 16) = 4770.13773`,
`log F = 8.4701305`, `E(0.863665) = 0.70779371`, margin over `109/154` is `1.50e-6`;
`F(0.905, 16) = 136.397401`, `E(0.722428) = 0.50000066`, margin over `1/2` is `6.6e-7`.
With the rounded bounds `F ≤ 4770.15` and `F ≤ 136.398` the margins are `2.66e-7` over
`109/154 + 10^-6` and `1.63e-7` over `1/2 + 10^-7`. These agree with the lab's gen/half78.out.
A random test of display 44, `h ≤ 6`, 300 random `β, ρ` per case, found no `avg` above the
value at `β = 0, ρ = 1`.

Page numbers are not visible in the arXiv text read for this unit; Section and display numbers
are given. The paper copy was NOT FOUND in either lab location; the text used is arXiv
math/0201299 through WebFetch, 2026-10-26.

ASSEMBLY, real proofs, CONDITIONAL ON the leaves: `F_eq_Fzero`, `lemma1_E_uncond`,
`lemma1_E_grh`, `circle_positive`.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.HeathBrownPuchta.Decomp1530Core215
import LeanLab.HeathBrownPuchta.Decomp1530CosA215
import LeanLab.HeathBrownPuchta.Decomp1530CosB215
import LeanLab.HeathBrownPuchta.Decomp1530UncondA215
import LeanLab.HeathBrownPuchta.Decomp1530UncondB215
import LeanLab.HeathBrownPuchta.Decomp1530GrhA215
import LeanLab.HeathBrownPuchta.Decomp1530GrhB215

namespace LeanLab.HeathBrownPuchta.Decomp1530c
open Finset Real LeanLab.HeathBrownPuchta.Decomp1530a LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.Linnik
attribute [local instance 10] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open LeanLab.HeathBrownPuchta.Decomp1530c.CoreExports215
open LeanLab.HeathBrownPuchta.Decomp1530c.CosA215Exports
open LeanLab.HeathBrownPuchta.Decomp1530c.CosB215Exports
open LeanLab.HeathBrownPuchta.Decomp1530c.UncondA215Exports
open LeanLab.HeathBrownPuchta.Decomp1530c.UncondB215Exports
open LeanLab.HeathBrownPuchta.Decomp1530c.GrhA215Exports
open LeanLab.HeathBrownPuchta.Decomp1530c.GrhB215Exports

private lemma ckc_all : ∀ c : Fin 64, ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * c.val + k.val) % 65536)
      (65536 - (512 * c.val + k.val) % 65536)) = rawI (512 * c.val + k.val) := by
  intro c k
  fin_cases c
  · exact ckc0 k
  · exact ckc1 k
  · exact ckc2 k
  · exact ckc3 k
  · exact ckc4 k
  · exact ckc5 k
  · exact ckc6 k
  · exact ckc7 k
  · exact ckc8 k
  · exact ckc9 k
  · exact ckc10 k
  · exact ckc11 k
  · exact ckc12 k
  · exact ckc13 k
  · exact ckc14 k
  · exact ckc15 k
  · exact ckc16 k
  · exact ckc17 k
  · exact ckc18 k
  · exact ckc19 k
  · exact ckc20 k
  · exact ckc21 k
  · exact ckc22 k
  · exact ckc23 k
  · exact ckc24 k
  · exact ckc25 k
  · exact ckc26 k
  · exact ckc27 k
  · exact ckc28 k
  · exact ckc29 k
  · exact ckc30 k
  · exact ckc31 k
  · exact ckc32 k
  · exact ckc33 k
  · exact ckc34 k
  · exact ckc35 k
  · exact ckc36 k
  · exact ckc37 k
  · exact ckc38 k
  · exact ckc39 k
  · exact ckc40 k
  · exact ckc41 k
  · exact ckc42 k
  · exact ckc43 k
  · exact ckc44 k
  · exact ckc45 k
  · exact ckc46 k
  · exact ckc47 k
  · exact ckc48 k
  · exact ckc49 k
  · exact ckc50 k
  · exact ckc51 k
  · exact ckc52 k
  · exact ckc53 k
  · exact ckc54 k
  · exact ckc55 k
  · exact ckc56 k
  · exact ckc57 k
  · exact ckc58 k
  · exact ckc59 k
  · exact ckc60 k
  · exact ckc61 k
  · exact ckc62 k
  · exact ckc63 k

private lemma cbu_all : ∀ c : Fin 64, ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * (4 * c.val + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[4 * c.val + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  intro c j
  fin_cases c
  · exact cbu0 j
  · exact cbu1 j
  · exact cbu2 j
  · exact cbu3 j
  · exact cbu4 j
  · exact cbu5 j
  · exact cbu6 j
  · exact cbu7 j
  · exact cbu8 j
  · exact cbu9 j
  · exact cbu10 j
  · exact cbu11 j
  · exact cbu12 j
  · exact cbu13 j
  · exact cbu14 j
  · exact cbu15 j
  · exact cbu16 j
  · exact cbu17 j
  · exact cbu18 j
  · exact cbu19 j
  · exact cbu20 j
  · exact cbu21 j
  · exact cbu22 j
  · exact cbu23 j
  · exact cbu24 j
  · exact cbu25 j
  · exact cbu26 j
  · exact cbu27 j
  · exact cbu28 j
  · exact cbu29 j
  · exact cbu30 j
  · exact cbu31 j
  · exact cbu32 j
  · exact cbu33 j
  · exact cbu34 j
  · exact cbu35 j
  · exact cbu36 j
  · exact cbu37 j
  · exact cbu38 j
  · exact cbu39 j
  · exact cbu40 j
  · exact cbu41 j
  · exact cbu42 j
  · exact cbu43 j
  · exact cbu44 j
  · exact cbu45 j
  · exact cbu46 j
  · exact cbu47 j
  · exact cbu48 j
  · exact cbu49 j
  · exact cbu50 j
  · exact cbu51 j
  · exact cbu52 j
  · exact cbu53 j
  · exact cbu54 j
  · exact cbu55 j
  · exact cbu56 j
  · exact cbu57 j
  · exact cbu58 j
  · exact cbu59 j
  · exact cbu60 j
  · exact cbu61 j
  · exact cbu62 j
  · exact cbu63 j

private lemma cbg_all : ∀ c : Fin 64, ∀ j : Fin 4,
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * (4 * c.val + j.val) + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[4 * c.val + j.val]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  intro c j
  fin_cases c
  · exact cbg0 j
  · exact cbg1 j
  · exact cbg2 j
  · exact cbg3 j
  · exact cbg4 j
  · exact cbg5 j
  · exact cbg6 j
  · exact cbg7 j
  · exact cbg8 j
  · exact cbg9 j
  · exact cbg10 j
  · exact cbg11 j
  · exact cbg12 j
  · exact cbg13 j
  · exact cbg14 j
  · exact cbg15 j
  · exact cbg16 j
  · exact cbg17 j
  · exact cbg18 j
  · exact cbg19 j
  · exact cbg20 j
  · exact cbg21 j
  · exact cbg22 j
  · exact cbg23 j
  · exact cbg24 j
  · exact cbg25 j
  · exact cbg26 j
  · exact cbg27 j
  · exact cbg28 j
  · exact cbg29 j
  · exact cbg30 j
  · exact cbg31 j
  · exact cbg32 j
  · exact cbg33 j
  · exact cbg34 j
  · exact cbg35 j
  · exact cbg36 j
  · exact cbg37 j
  · exact cbg38 j
  · exact cbg39 j
  · exact cbg40 j
  · exact cbg41 j
  · exact cbg42 j
  · exact cbg43 j
  · exact cbg44 j
  · exact cbg45 j
  · exact cbg46 j
  · exact cbg47 j
  · exact cbg48 j
  · exact cbg49 j
  · exact cbg50 j
  · exact cbg51 j
  · exact cbg52 j
  · exact cbg53 j
  · exact cbg54 j
  · exact cbg55 j
  · exact cbg56 j
  · exact cbg57 j
  · exact cbg58 j
  · exact cbg59 j
  · exact cbg60 j
  · exact cbg61 j
  · exact cbg62 j
  · exact cbg63 j

/-- The packed table agrees with the rounded Taylor polynomial at every residue below `32769`. -/
private lemma hcos : ∀ i : Fin 32769, mcos (2 * 314159265358979323846 *
    min (i.val % 65536) (65536 - i.val % 65536)) = rawI i.val := by
  intro i
  by_cases h : i.val = 32768
  · rw [h]
    decide
  · have hc : i.val / 512 < 64 := by have := i.isLt; omega
    have hk : i.val % 512 < 512 := Nat.mod_lt _ (by norm_num)
    have key := ckc_all ⟨i.val / 512, hc⟩ ⟨i.val % 512, hk⟩
    have hdm : 512 * (i.val / 512) + i.val % 512 = i.val := by omega
    rwa [hdm] at key

private lemma ckE_uncond (b : ℕ) (hb : b < 256) :
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (1181 * cc (128 * b + r + 1)) (10 ^ 13))
      ≤ (((blockUncond177[b]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have key := cbu_all ⟨b / 4, by omega⟩ ⟨b % 4, Nat.mod_lt _ (by norm_num)⟩
  have hdm : 4 * (b / 4) + b % 4 = b := by omega
  rwa [hdm] at key

private lemma ckE_grh (b : ℕ) (hb : b < 256) :
    (1000 : ℤ) * (∑ r ∈ range 128, mexp (905 * cc (128 * b + r + 1)) (10 ^ 13))
      ≤ (((blockGrh177[b]?.getD 0 : ℕ)) : ℤ) * 10 ^ 8 := by
  have key := cbg_all ⟨b / 4, by omega⟩ ⟨b % 4, Nat.mod_lt _ (by norm_num)⟩
  have hdm : 4 * (b / 4) + b % 4 = b := by omega
  rwa [hdm] at key

private def Sbound (bnds : Array ℕ) : ℕ := ∑ b ∈ range 256, (bnds[b]?.getD 0 : ℕ)

private lemma Sbound_eq (bnds : Array ℕ) :
    (∑ b ∈ range 256, ((bnds[b]?.getD 0 : ℕ) : ℚ) / 1000) = ((Sbound bnds : ℕ) : ℚ) / 1000 := by
  unfold Sbound
  have hc : (((∑ b ∈ range 256, (bnds[b]?.getD 0 : ℕ)) : ℕ) : ℚ)
      = ∑ b ∈ range 256, ((bnds[b]?.getD 0 : ℕ) : ℚ) := by
    push_cast
    rfl
  rw [hc, Finset.sum_div]

private lemma ckEnd_uncond :
    ((mexp (1181 * cc 0) (10 ^ 13) - mexp (1181 * cc 32768) (10 ^ 13)) * ((1000 : ℤ) * 100))
      + 2 * (Sbound blockUncond177 : ℤ) * ((10 ^ 8 : ℤ) * 100)
      ≤ (477015 : ℤ) * ((10 ^ 8 : ℤ) * 1000 * 65536) := by decide +kernel

private lemma ckEnd_grh :
    ((mexp (905 * cc 0) (10 ^ 13) - mexp (905 * cc 32768) (10 ^ 13)) * ((1000 : ℤ) * 1000))
      + 2 * (Sbound blockGrh177 : ℤ) * ((10 ^ 8 : ℤ) * 1000)
      ≤ (136398 : ℤ) * ((10 ^ 8 : ℤ) * 1000 * 65536) := by decide +kernel

/-- LEAF. Section 7, pages 30 and 31, display 44 at xi equal to 1.181.
The remaining task is a closed inequality of rational finite sums. -/
theorem Ffold_uncond177 : Ffold177 (1181 / 1000) ≤ 477015 / 100 := by
  have hcor : ∀ r < 32769, cosUpper177 65536 r = cosLookup177 r :=
    fun r hr => cosUpper_of_check r (hcos ⟨r, hr⟩)
  refine Ffold_bound_of_blocks177 hcor (1181 / 1000) (477015 / 100) blockUncond177 ?_ ?_
  · intro b
    exact blk_le 1181 b.val (blockUncond177[b.val]?.getD 0) (ckE_uncond b.val b.isLt)
  · have h0 := cachedTerm_eq (1181 : ℤ) 0
    have h1 := cachedTerm_eq (1181 : ℤ) 32768
    have hq : (1181 : ℚ) = ((1181 : ℤ) : ℚ) := by norm_num
    rw [hq, h0, h1, Sbound_eq]
    exact hend_le _ _ _ 477015 100 (by norm_num) (ckEnd_uncond)

/-- LEAF. Section 7, pages 30 and 31, display 44 at xi equal to 0.905.
The remaining task is a closed inequality of rational finite sums. -/
theorem Ffold_grh177 : Ffold177 (905 / 1000) ≤ 136398 / 1000 := by
  have hcor : ∀ r < 32769, cosUpper177 65536 r = cosLookup177 r :=
    fun r hr => cosUpper_of_check r (hcos ⟨r, hr⟩)
  refine Ffold_bound_of_blocks177 hcor (905 / 1000) (136398 / 1000) blockGrh177 ?_ ?_
  · intro b
    exact blk_le 905 b.val (blockGrh177[b.val]?.getD 0) (ckE_grh b.val b.isLt)
  · have h0 := cachedTerm_eq (905 : ℤ) 0
    have h1 := cachedTerm_eq (905 : ℤ) 32768
    have hq : (905 : ℚ) = ((905 : ℤ) : ℚ) := by norm_num
    rw [hq, h0, h1, Sbound_eq]
    exact hend_le _ _ _ 136398 1000 (by norm_num) (ckEnd_grh)

/-! ### Leaves: the explicit values at `h = 16` -/

/-- LEAF. Unit U-1530. `F(1.181, 16) ≤ 4770.15`, a finite sum over `2^16` residues, numpy value
`4770.13773`; Section 7, the choice `h = 16`, `ξ = 1.181`. -/
theorem Fzero_uncond : Fzero (1181 / 1000) 16 ≤ 477015 / 100 := by
  have hb := Fzero_le_Fupper177 (1181/1000) (by norm_num) (by norm_num) 16 (by omega)
  rw [Fupper_eq_fold177] at hb
  have hc := (Rat.cast_le (K := ℝ)).mpr Ffold_uncond177
  norm_num at hb hc ⊢
  exact hb.trans hc

/-- LEAF. Unit U-1530. `F(0.905, 16) ≤ 136.398`, a finite sum over `2^16` residues, numpy value
`136.397401`; Section 7, the choice `h = 16`, `ξ = 0.905`. -/
theorem Fzero_grh : Fzero (905 / 1000) 16 ≤ 136398 / 1000 := by
  have hb := Fzero_le_Fupper177 (905/1000) (by norm_num) (by norm_num) 16 (by omega)
  rw [Fupper_eq_fold177] at hb
  have hc := (Rat.cast_le (K := ℝ)).mpr Ffold_grh177
  norm_num at hb hc ⊢
  exact hb.trans hc

/-- LEAF. Unit U-1530. `1.181 · 0.863665/log 2 - log 4770.15/(16 log 2) > 109/154 + 10^-6`,
double precision margin `2.66e-7`; Section 7, `E(0.863665) > 109/154`. -/
theorem E_num_uncond :
    109 / 154 + 1 / 10 ^ 6 < Emodel (1181 / 1000) (863665 / 1000000) (477015 / 100) 16 := by
  unfold Emodel
  norm_num only [Nat.cast_ofNat]
  have hl : Real.log (477015 / 100) < (8470135 / 1000000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have hh := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 8470135 / 1000000 by norm_num) 42
    have hsum : (477015 / 100 : ℝ) < ∑ i ∈ range 42, (8470135 / 1000000 : ℝ) ^ i / i.factorial := by
      norm_num [sum_range_succ, Nat.factorial]
    exact hsum.trans_le hh
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.log_two_lt_d9
  have he : (109 / 154 + 1 / 10 ^ 6 : ℝ) * (16 * Real.log 2) < 16 * (1181 / 1000) * (863665 / 1000000) - Real.log (477015 / 100) := by nlinarith
  have hd := (lt_div_iff₀ (show 0 < 16 * Real.log 2 by positivity)).mpr he
  convert hd using 1 <;> norm_num <;> field_simp <;> ring

/-- LEAF. Unit U-1530. `0.905 · 0.722428/log 2 - log 136.398/(16 log 2) > 1/2 + 10^-7`,
double precision margin `1.63e-7`; Section 7, `E(0.722428) > 1/2`. -/
theorem E_num_grh :
    1 / 2 + 1 / 10 ^ 7 < Emodel (905 / 1000) (722428 / 1000000) (136398 / 1000) 16 := by
  unfold Emodel
  norm_num only [Nat.cast_ofNat]
  have hl : Real.log (136398 / 1000) < (4915578 / 1000000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have hh := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4915578 / 1000000 by norm_num) 32
    have hsum : (136398 / 1000 : ℝ) < ∑ i ∈ range 32, (4915578 / 1000000 : ℝ) ^ i / i.factorial := by
      norm_num [sum_range_succ, Nat.factorial]
    exact hsum.trans_le hh
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.log_two_lt_d9
  have he : (1 / 2 + 1 / 10 ^ 7 : ℝ) * (16 * Real.log 2) < 16 * (905 / 1000) * (722428 / 1000000) - Real.log (136398 / 1000) := by nlinarith
  have hd := (lt_div_iff₀ (show 0 < 16 * Real.log 2 by positivity)).mpr he
  convert hd using 1 <;> norm_num <;> field_simp <;> ring

/-! ### Leaf: the circle method identity -/

/-- LEAF. Unit U-1530. `R(N) = ∫₀¹ S(α)² T(α)^K e(-αN) dα` equals the number of
representations `N = p + p' + 2^{ν₁} + ... + 2^{ν_K}` with `ϖN < p, p' ≤ N`, `1 ≤ ν_i ≤ L`;
Section 2, by orthogonality. -/
theorem circle_count (N : ℕ) (w : ℝ) (L K : ℕ) : Rint N w L K = ((reps N w L K).card : ℂ) := by
  classical
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hprod (α : ℝ) (ν : Fin K → ℕ) :
      (∏ i, ee (α * 2 ^ (ν i))) = ee (α * ∑ i, (2 : ℝ) ^ (ν i)) := by
    unfold ee
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [mul_sum]
  have hexp (n : ℤ) : Continuous (fun α : ℝ => ee (α * n)) := by unfold ee; fun_prop
  have heq (α : ℝ) : Sp N w α ^ 2 * Tp L α ^ K * ee (-(α * N)) =
      ∑ p ∈ primesIn N w, ∑ q ∈ primesIn N w,
        ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
          ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ)) := by
    unfold Sp Tp
    rw [pow_two, Finset.sum_pow']
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro ν hν
    rw [hprod, ← hadd, ← hadd, ← hadd]
    congr 1
    push_cast
    ring
  have hν (p q : ℕ) :
      (∫ α in (0 : ℝ)..1, ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
        ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ))) =
      ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
        ∫ α in (0 : ℝ)..1, ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ)) :=
    intervalIntegral.integral_finsetSum (fun ν hν => (hexp _).intervalIntegrable 0 1)
  have hq (p : ℕ) :
      (∫ α in (0 : ℝ)..1, ∑ q ∈ primesIn N w,
        ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
          ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ))) =
      ∑ q ∈ primesIn N w, ∫ α in (0 : ℝ)..1,
        ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
          ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ)) := by
    apply intervalIntegral.integral_finsetSum
    intro q hq
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop
  unfold Rint
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum (fun p hp => by
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop)]
  simp_rw [hq, hν, orth]
  have hz (p q : ℕ) (ν : Fin K → ℕ) :
      ((p : ℤ) + q + ∑ i, (2 : ℤ) ^ ν i - N = 0) ↔ p + q + ∑ i, 2 ^ ν i = N := by
    rw [sub_eq_zero]
    exact_mod_cast (Iff.rfl : p + q + ∑ i, 2 ^ ν i = N ↔ p + q + ∑ i, 2 ^ ν i = N)
  simp_rw [hz]
  unfold reps
  simp only [Finset.card_eq_sum_ones, sum_filter, sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-! ### Assemblies -/

/-- ASSEMBLY, CONDITIONAL ON `TL_re_at`, `avg_le_avg_zero` and `avg_le_F` of file a: display 44,
`F(ξ, h)` equals its value at `β = 0`, `ρ = 1`, for `ξ ≥ 0`. -/
theorem F_eq_Fzero {ξ : ℝ} (hξ : 0 ≤ ξ) (hh : ℕ) : F ξ hh = Fzero ξ hh := by
  have h0 : avg ξ 1 hh 0 = Fzero ξ hh := by
    unfold avg Fzero
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [one_mul, zero_add, TL_re_at]
  rw [← h0]
  apply le_antisymm
  · haveI : Nonempty {p : ℝ × ℂ // p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ‖p.2‖ = 1} :=
      ⟨⟨(0, 1), ⟨le_rfl, zero_le_one⟩, by simp⟩⟩
    exact ciSup_le fun p => avg_le_avg_zero ξ hξ p.2.2 hh p.1.1
  · exact avg_le_F ξ hh ⟨le_rfl, zero_le_one⟩ (by simp)

theorem Emodel_anti {ξ lam F0 F1 : ℝ} {hh : ℕ} (hhp : 0 < hh) (hF0 : 0 < F0) (hF : F0 ≤ F1) :
    Emodel ξ lam F1 hh ≤ Emodel ξ lam F0 hh := by
  unfold Emodel
  have hl : 0 < (hh : ℝ) * Real.log 2 :=
    mul_pos (by exact_mod_cast hhp) (Real.log_pos (by norm_num))
  have := Real.log_le_log hF0 hF
  have : Real.log F0 / (hh * Real.log 2) ≤ Real.log F1 / (hh * Real.log 2) :=
    div_le_div_of_nonneg_right this hl.le
  linarith

/-- ASSEMBLY, CONDITIONAL ON the leaves of `F_eq_Fzero` and on `Fzero_ge_one`, `Fzero_uncond`,
`E_num_uncond`: Lemma 1's unconditional exponent, `E(0.863665) > 109/154 + 10^-6` at
`ξ = 1.181`, `h = 16`, Section 7. -/
theorem lemma1_E_uncond :
    109 / 154 + 1 / 10 ^ 6 < Emodel (1181 / 1000) (863665 / 1000000) (F (1181 / 1000) 16) 16 := by
  rw [F_eq_Fzero (by norm_num)]
  have h1 := Fzero_ge_one (1181 / 1000) 16
  exact lt_of_lt_of_le E_num_uncond
    (Emodel_anti (by norm_num) (by linarith) Fzero_uncond)

/-- ASSEMBLY, CONDITIONAL ON the leaves of `F_eq_Fzero` and on `Fzero_ge_one`, `Fzero_grh`,
`E_num_grh`: Lemma 1's GRH exponent, `E(0.722428) > 1/2 + 10^-7` at `ξ = 0.905`, `h = 16`,
Section 7. -/
theorem lemma1_E_grh :
    1 / 2 + 1 / 10 ^ 7 < Emodel (905 / 1000) (722428 / 1000000) (F (905 / 1000) 16) 16 := by
  rw [F_eq_Fzero (by norm_num)]
  have h1 := Fzero_ge_one (905 / 1000) 16
  exact lt_of_lt_of_le E_num_grh
    (Emodel_anti (by norm_num) (by linarith) Fzero_grh)

/-- ASSEMBLY, CONDITIONAL ON `circle_count`: if `Re R(N) > 0` then `N` is two primes plus
exactly `K` powers of 2 with exponents at least 1, the identity used in Section 6 and the
`circle` hypothesis of Assembly.lean. -/
theorem circle_positive {N : ℕ} {w : ℝ} {L K : ℕ} (hR : 0 < (Rint N w L K).re) :
    LinnikExact K N := by
  rw [circle_count, Complex.natCast_re] at hR
  have hc : 0 < (reps N w L K).card := by exact_mod_cast hR
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hc
  unfold reps at hx
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hx
  obtain ⟨⟨hp, hq, hν⟩, hsum⟩ := hx
  unfold primesIn at hp hq
  simp only [Finset.mem_filter] at hp hq
  exact ⟨x.1, x.2.1, hp.2.1, hq.2.1, x.2.2, fun i => (Finset.mem_Icc.1 (hν i)).1, hsum.symm⟩

end LeanLab.HeathBrownPuchta.Decomp1530c
