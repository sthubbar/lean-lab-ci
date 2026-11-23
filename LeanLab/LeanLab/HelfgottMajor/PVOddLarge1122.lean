import Mathlib
import LeanLab.HelfgottMajor.PVOddTrunc1122
import LeanLab.HelfgottMajor.PVOddCot1122
import LeanLab.HelfgottMajor.PVTailAbel1122

/-!
Route burst S75, burst-20261122, tag odd-large. Split of the HARD LEAF
`PVOddTrunc1122.odd_truncated_large` along Pomerance 2011, Integers 11A Article 19, Section 4,
the bounds for C_n and D_n on page 9 and the choice n = ⌊(4/π) √q log q⌋ on page 10, with the
cotangent form of the Polya expansion, the PROVED identity `PVOddCot1122.polya_interval_cot`,
in place of Pomerance's Fourier series. The assembly `odd_truncated_large` has exactly the
statement of the LEAF, checked by `type_of%`.

Route. The identity gives ‖S‖ ≤ 1 + ‖W‖/(2√q) with W the cotangent sum over h. The head
h ≤ H or h ≥ q - H folds onto 1 ≤ m ≤ H as in `PVOddFold1122`, and cot(πm/q) ≤ q/(πm) gives
Pomerance's C_n term. The tail goes through display 7 duality `PVTailAbel1122.dual_bound`, the
Abel bound of Lemma 4 and the cosecant sum of display 5: its share is at most
4q/(π²(H+1)) (log q + log(4/π) + π²/(12q²)), Pomerance's bound for |D_n|. The closing
inequality at Pomerance's n is a numerical check.

Numerical screen, Python, double precision: the closing inequality holds for every q from 1001
to 200000, slack above 0.155 √q. The Abel and duality steps were checked on Legendre
characters for q up to 1013, worst ratio to the bound 0.56.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddLarge1122

open Real Finset

theorem stdAddChar_pow_mul {q : ℕ} [NeZero q] (h a : ZMod q) (n : ℕ) :
    ZMod.stdAddChar h ^ n * ZMod.stdAddChar (a * h) = ZMod.stdAddChar ((a + (n : ZMod q)) * h) := by
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul, nsmul_eq_mul, add_mul, add_comm]

theorem odd_tail_dual_proof {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (H M N : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ ≤
      2 / sqrt q * ∑ b : ZMod q, ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ := by
  set S := univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val))
  set V : ZMod q → ℂ := fun b => ∑ h ∈ S, (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)
  have hd := LeanLab.HelfgottMajor.PVTailAbel1122.dual_bound hχ S
    (fun h => (Real.cot (π * h.val / q) : ℂ) *
      (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M))
  have hL : ∑ h ∈ S, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) =
      ∑ h ∈ S, χ⁻¹ h * ((Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)) :=
    sum_congr rfl fun h _ => by ring
  have hI : ∀ a : ZMod q, ∑ h ∈ S, (Real.cot (π * h.val / q) : ℂ) *
      (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) * ZMod.stdAddChar (a * h) =
      V (a + ((N + 1 : ℕ) : ZMod q)) - V (a + (M : ZMod q)) := by
    intro a
    simp only [V, ← sum_sub_distrib]
    refine sum_congr rfl fun h _ => ?_
    rw [← stdAddChar_pow_mul h a (N + 1), ← stdAddChar_pow_mul h a M]
    ring
  rw [hL] at ⊢
  refine hd.trans ?_
  simp_rw [hI]
  have hs : 0 ≤ 1 / sqrt (q : ℝ) := by positivity
  have hsh : ∀ c : ZMod q, ∑ a : ZMod q, ‖V (a + c)‖ = ∑ b : ZMod q, ‖V b‖ := fun c =>
    Equiv.sum_comp (Equiv.addRight c) (fun b => ‖V b‖)
  calc 1 / sqrt (q : ℝ) * ∑ a : ZMod q, ‖V (a + ((N + 1 : ℕ) : ZMod q)) - V (a + (M : ZMod q))‖
      ≤ 1 / sqrt (q : ℝ) * ∑ a : ZMod q, (‖V (a + ((N + 1 : ℕ) : ZMod q))‖ + ‖V (a + (M : ZMod q))‖) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => norm_sub_le _ _) hs
    _ = 2 / sqrt q * ∑ b : ZMod q, ‖V b‖ := by
        rw [sum_add_distrib, hsh, hsh]; ring

end LeanLab.HelfgottMajor.PVOddLarge1122

namespace LeanLab.HelfgottMajor.PVOddLarge1122.OddHeadAux

open Real Finset
theorem std_pow_add_neg {q : ℕ} [NeZero q] (h : ZMod q) (n : ℕ) :
    ZMod.stdAddChar h ^ n + ZMod.stdAddChar (-h) ^ n =
      2 * ((Real.cos (2 * π * h.val * n / q) : ℝ) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, inv_pow, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> push_cast <;> ring

/-- cot(π(q-h)/q) = -cot(π h/q) for h ≠ 0 in ZMod q. PROVED. -/
theorem cot_neg_val {q : ℕ} [NeZero q] {h : ZMod q} (hh : h ≠ 0) :
    Real.cot (π * (-h).val / q) = - Real.cot (π * h.val / q) := by
  have : NeZero h := ⟨hh⟩
  rw [ZMod.val_neg_of_ne_zero]
  have hle : h.val ≤ q := (ZMod.val_lt h).le
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [Nat.cast_sub hle]
  rw [show π * ((q : ℝ) - h.val) / q = π - π * h.val / q by field_simp]
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

/-- Frolenkov display 14 step, the pairing of h with -h for odd χ in the cotangent form of the
Polya identity: the two terms add to twice χ⁻¹(h) cot(π h/q) (cos hβ - cos hα). PROVED. -/
theorem pair_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1)
    (hm : χ⁻¹ (-1) = -1) (M N : ℕ) (h : ZMod q) :
    (χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)) +
    (χ⁻¹ (-h) * (Real.cot (π * (-h).val / q) : ℂ) *
        (ZMod.stdAddChar (-h) ^ (N + 1) - ZMod.stdAddChar (-h) ^ M)) =
      2 * (χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ))) := by
  by_cases hh : h = 0
  · subst hh; simp [DirichletCharacter.map_zero' _ hq]
  · have e1 : χ⁻¹ (-h) = -χ⁻¹ h := by
      rw [show -h = (-1) * h by ring, map_mul, hm]; ring
    rw [e1, cot_neg_val hh, Complex.ofReal_neg]
    have a := std_pow_add_neg h (N + 1)
    have b := std_pow_add_neg h M
    linear_combination (χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ)) * (a - b)


/-- The cotangent sum of the Polya identity for odd χ equals its cosine form. PROVED. -/
theorem sum_pair {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1)
    (hm : χ⁻¹ (-1) = -1) (M N : ℕ) :
    ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) =
      ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ)) := by
  set f : ZMod q → ℂ := fun h => χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) with hf
  have hneg : ∑ h : ZMod q, f (-h) = ∑ h : ZMod q, f h := Equiv.sum_comp (Equiv.neg (ZMod q)) f
  have h2 : (2 : ℂ) * ∑ h : ZMod q, f h = 2 * ∑ h : ZMod q, χ⁻¹ h *
      (Real.cot (π * h.val / q) : ℂ) * (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ)) := by
    calc (2 : ℂ) * ∑ h : ZMod q, f h = ∑ h : ZMod q, f h + ∑ h : ZMod q, f (-h) := by
          rw [hneg]; ring
      _ = ∑ h : ZMod q, (f h + f (-h)) := Finset.sum_add_distrib.symm
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun h _ => pair_term χ hq hm M N h
  exact mul_left_cancel₀ two_ne_zero h2

/-- Norm bound of the cosine form, |χ⁻¹| ≤ 1. PROVED. -/
theorem norm_cos_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (M N : ℕ) :
    ‖∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ))‖ ≤
      ∑ h : ZMod q, |Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  rw [norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have := DirichletCharacter.norm_le_one χ⁻¹ h
  have h0 : 0 ≤ |Real.cot (π * h.val / q)| *
      |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)| := by
    positivity
  calc ‖χ⁻¹ h‖ * |Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|
      = ‖χ⁻¹ h‖ * (|Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|) := by ring
    _ ≤ 1 * (|Real.cot (π * h.val / q)| *
        |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|) := by
        gcongr
    _ = _ := one_mul _


/-- The summand |cot(π v/q)| |cos(2π v (N+1)/q) - cos(2π v M/q)| is symmetric under
v ↦ q - v. PROVED. -/
theorem G_reflect {q : ℕ} (hq : 0 < q) (M N v : ℕ) (hv : v ≤ q) :
    |Real.cot (π * ((q - v : ℕ) : ℝ) / q)| *
        |Real.cos (2 * π * ((q - v : ℕ) : ℝ) * (N + 1 : ℕ) / q) -
          Real.cos (2 * π * ((q - v : ℕ) : ℝ) * M / q)| =
      |Real.cot (π * (v : ℝ) / q)| *
        |Real.cos (2 * π * (v : ℝ) * (N + 1 : ℕ) / q) - Real.cos (2 * π * (v : ℝ) * M / q)| := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Nat.cast_sub hv]
  have e1 : π * ((q : ℝ) - v) / q = π - π * v / q := by field_simp
  have e2 : ∀ n : ℕ, 2 * π * ((q : ℝ) - v) * n / q = n * (2 * π) - 2 * π * v * n / q := by
    intro n; field_simp
  rw [e1, e2, e2, Real.cos_nat_mul_two_pi_sub, Real.cos_nat_mul_two_pi_sub,
    Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div,
    abs_neg]

/-- A sum over ZMod q of a function of the least residue is the sum over range q. PROVED. -/
theorem sum_zmod_val {q : ℕ} [NeZero q] (G : ℕ → ℝ) :
    ∑ h : ZMod q, G h.val = ∑ v ∈ range q, G v := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := NeZero.ne q; omega⟩
  exact Fin.sum_univ_eq_sum_range G (k + 1)


/-- Folding a sum over range q of a function vanishing at 0 and at q/2, symmetric under
v ↦ q - v, onto 1 ≤ v ≤ (q-1)/2 with factor 2. PROVED. -/
theorem fold_range {q : ℕ} (hq7 : 7 ≤ q) (G : ℕ → ℝ) (h0 : G 0 = 0)
    (hrefl : ∀ v ≤ q, G (q - v) = G v) (hhalf : 2 ∣ q → G (q / 2) = 0) :
    ∑ v ∈ range q, G v = 2 * ∑ v ∈ Icc 1 ((q - 1) / 2), G v := by
  set K := (q - 1) / 2 with hK
  have hKq : K + 1 ≤ q := by omega
  rw [← Finset.sum_range_add_sum_Ico G hKq]
  have hA : ∑ v ∈ range (K + 1), G v = ∑ v ∈ Icc 1 K, G v := by
    rw [Finset.sum_range_succ', h0, add_zero]
    have : Icc 1 K = Ico 1 (K + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun v _ => by rw [add_comm]
  have hB : ∑ v ∈ Ico (K + 1) q, G v = ∑ v ∈ Icc 1 (q - K - 1), G v := by
    refine Finset.sum_nbij' (fun v => q - v) (fun w => q - w) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Ico, mem_Icc, coe_Ico, coe_Icc, Set.mem_Ico, Set.mem_Icc] at ha ⊢
      omega
    · intro a ha; simp only [mem_Ico, mem_Icc, coe_Ico, coe_Icc, Set.mem_Ico, Set.mem_Icc] at ha ⊢
      omega
    · intro a ha; simp only [mem_Ico, coe_Ico, Set.mem_Ico] at ha; omega
    · intro a ha; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at ha; omega
    · intro a ha; simp only [mem_Ico, coe_Ico, Set.mem_Ico] at ha
      exact (hrefl a ha.2.le).symm
  rw [hA, hB]
  rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
  · have e : q - K - 1 = K + 1 := by omega
    rw [e, Finset.sum_Icc_succ_top (by omega)]
    have : K + 1 = q / 2 := by omega
    rw [this, hhalf ⟨r, by omega⟩]
    ring
  · have e : q - K - 1 = K := by omega
    rw [e]; ring


end LeanLab.HelfgottMajor.PVOddLarge1122.OddHeadAux

namespace LeanLab.HelfgottMajor.PVOddLarge1122

open Real Finset
open LeanLab.HelfgottMajor.PVOddLarge1122.OddHeadAux

theorem odd_head_fold_proof {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (H : ℕ) (hH : 1 ≤ H) (hHq : 2 * H < q) (M N : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val),
        χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ ≤
      2 * ∑ m ∈ Icc 1 H,
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  have hq0 : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hm1 : χ (-1) = -1 := by
    have h1 : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hodd
    · linear_combination h
  have hm : χ⁻¹ (-1) = -1 := by
    rw [MulChar.inv_apply_eq_inv', hm1]; norm_num
  set P : ℕ → Prop := fun v => v ≤ H ∨ q - H ≤ v with hP
  -- the head set is closed under negation
  have hnegS : ∀ h : ZMod q, (P (-h).val ↔ P h.val) := by
    intro h
    by_cases hh : h = 0
    · subst hh; simp
    · have : NeZero h := ⟨hh⟩
      rw [ZMod.val_neg_of_ne_zero]
      have := ZMod.val_lt h
      simp only [hP]; omega
  set f : ZMod q → ℂ := fun h => χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M) with hf
  set g : ZMod q → ℂ := fun h => χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (((Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) : ℝ) : ℂ) -
          ((Real.cos (2 * π * h.val * M / q) : ℝ) : ℂ)) with hg
  have hfg : ∑ h ∈ univ.filter (fun h : ZMod q => P h.val), f h =
      ∑ h ∈ univ.filter (fun h : ZMod q => P h.val), g h := by
    rw [Finset.sum_filter, Finset.sum_filter]
    have hneg : ∑ h : ZMod q, (if P (-h).val then f (-h) else 0) =
        ∑ h : ZMod q, (if P h.val then f h else 0) :=
      Equiv.sum_comp (Equiv.neg (ZMod q)) (fun h => if P h.val then f h else 0)
    have h2 : (2 : ℂ) * ∑ h : ZMod q, (if P h.val then f h else 0) =
        2 * ∑ h : ZMod q, (if P h.val then g h else 0) := by
      calc (2 : ℂ) * ∑ h : ZMod q, (if P h.val then f h else 0)
          = ∑ h : ZMod q, (if P h.val then f h else 0) +
              ∑ h : ZMod q, (if P (-h).val then f (-h) else 0) := by rw [hneg]; ring
        _ = ∑ h : ZMod q, ((if P h.val then f h else 0) + (if P (-h).val then f (-h) else 0)) :=
            Finset.sum_add_distrib.symm
        _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          by_cases hp : P h.val
          · have hp' : P (-h).val := (hnegS h).mpr hp
            rw [if_pos hp, if_pos hp', if_pos hp]
            exact pair_term χ (by omega) hm M N h
          · have hp' : ¬ P (-h).val := fun h' => hp ((hnegS h).mp h')
            rw [if_neg hp, if_neg hp', if_neg hp]; simp
    exact mul_left_cancel₀ two_ne_zero h2
  show ‖∑ h ∈ univ.filter (fun h : ZMod q => P h.val), f h‖ ≤ _
  rw [hfg]
  set G : ℕ → ℝ := fun v => |Real.cot (π * (v : ℝ) / q)| *
    |Real.cos (2 * π * (v : ℝ) * (N + 1 : ℕ) / q) - Real.cos (2 * π * (v : ℝ) * M / q)| with hG
  set G' : ℕ → ℝ := fun v => if P v then G v else 0 with hG'
  have hnorm : ‖∑ h ∈ univ.filter (fun h : ZMod q => P h.val), g h‖ ≤
      ∑ h : ZMod q, G' h.val := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun h _ => ?_
    simp only [hG']
    split_ifs with hp
    · simp only [hg, hG]
      rw [norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have := DirichletCharacter.norm_le_one χ⁻¹ h
      have h0 : 0 ≤ |Real.cot (π * h.val / q)| *
          |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)| := by
        positivity
      calc ‖χ⁻¹ h‖ * |Real.cot (π * h.val / q)| *
            |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|
          = ‖χ⁻¹ h‖ * (|Real.cot (π * h.val / q)| *
            |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|) := by
            ring
        _ ≤ 1 * (|Real.cot (π * h.val / q)| *
            |Real.cos (2 * π * h.val * (N + 1 : ℕ) / q) - Real.cos (2 * π * h.val * M / q)|) := by
            gcongr
        _ = _ := one_mul _
    · simp
  refine hnorm.trans ?_
  rw [sum_zmod_val (q := q) G']
  have h0 : G' 0 = 0 := by
    simp only [hG', hG, Nat.cast_zero, mul_zero, zero_div, Real.cot_eq_cos_div_sin, Real.sin_zero,
      div_zero, abs_zero, zero_mul, ite_self]
  have hrefl : ∀ v ≤ q, G' (q - v) = G' v := by
    intro v hv
    have hPv : P (q - v) ↔ P v := by simp only [hP]; omega
    simp only [hG']
    rw [if_congr hPv rfl rfl]
    split_ifs
    · exact G_reflect hq0 M N v hv
    · rfl
  have hhalf : 2 ∣ q → G' (q / 2) = 0 := by
    intro h2
    have e : π * (((q / 2 : ℕ) : ℝ)) / q = π / 2 := by
      rw [Nat.cast_div h2 (by norm_num)]; push_cast; field_simp
    simp only [hG', hG, e, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div, abs_zero,
      zero_mul, ite_self]
  rw [fold_range hq7 G' h0 hrefl hhalf]
  gcongr 2 * ?_
  have hsplit : ∑ v ∈ Icc 1 ((q - 1) / 2), G' v = ∑ v ∈ Icc 1 H, G v := by
    simp only [hG']
    rw [← Finset.sum_filter]
    congr 1
    ext v; simp only [mem_filter, mem_Icc, hP]; omega
  rw [hsplit]
  refine le_of_eq (Finset.sum_congr rfl fun m hm => ?_)
  rw [mem_Icc] at hm
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : (2 : ℝ) * m < q := by exact_mod_cast (show 2 * m < q by omega)
  have hx0 : 0 < π * m / q := by positivity
  have hx1 : π * m / q < π / 2 := by
    rw [div_lt_div_iff₀ hqr (by norm_num)]
    nlinarith [pi_pos]
  have hc : 0 ≤ Real.cot (π * m / q) := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hx1.le⟩)
      (Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith))
  simp only [hG]
  rw [abs_of_nonneg hc, abs_sub_comm]
  congr 3 <;> push_cast <;> ring_nf


end LeanLab.HelfgottMajor.PVOddLarge1122

open Real Finset

namespace LeanLab.HelfgottMajor.PVOddLarge1122Aux.Close

lemma exp6_le : exp (6:ℝ) ≤ 1001 := by
  have : exp (6:ℝ) = exp 1 ^ 6 := by rw [← exp_nat_mul]; norm_num
  rw [this]
  have h := exp_one_lt_d9
  calc exp 1 ^ 6 ≤ (2.72:ℝ) ^ 6 := pow_le_pow_left₀ (exp_pos 1).le (by linarith) 6
    _ ≤ 1001 := by norm_num

theorem odd_one {q : ℕ} (hq : 1000 < q) :
    1 ≤ ⌊4 / π * sqrt q * log q⌋₊ ∧ (235:ℝ) < ⌊4 / π * sqrt q * log q⌋₊ := by
  have hqR : (1001:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hss : sqrt (q:ℝ) * sqrt (q:ℝ) = q := mul_self_sqrt hq0.le
  have hs31 : 31 ≤ sqrt (q:ℝ) := by
    rw [show (31:ℝ) = sqrt 961 by rw [show (961:ℝ) = 31^2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by linarith)
  have hL6 : 6 ≤ log (q:ℝ) := by
    rw [le_log_iff_exp_le hq0]; linarith [exp6_le]
  set s := sqrt (q:ℝ) with hs
  set L := log (q:ℝ) with hLdef
  have hpi := pi_lt_d2
  have hc : (1.2698:ℝ) ≤ 4 / π := by rw [le_div_iff₀ pi_pos]; nlinarith
  set x := 4 / π * s * L with hx
  have hx0 : 0 ≤ x := by positivity
  have hxH : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hsL : 186 ≤ s * L := by nlinarith
  have hx236 : 236 ≤ x := by rw [hx, mul_assoc]; nlinarith
  have hH : (235:ℝ) < ⌊x⌋₊ := by linarith
  refine ⟨?_, hH⟩
  have : (1:ℝ) ≤ ⌊x⌋₊ := by linarith
  exact_mod_cast this

theorem odd_two {q : ℕ} (hq : 1000 < q) :
    2 * (⌊4 / π * sqrt q * log q⌋₊ + 1) < q := by
  have hqR : (1001:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hss : sqrt (q:ℝ) * sqrt (q:ℝ) = q := mul_self_sqrt hq0.le
  have hs31 : 31 ≤ sqrt (q:ℝ) := by
    rw [show (31:ℝ) = sqrt 961 by rw [show (961:ℝ) = 31^2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by linarith)
  have hLs : log (q:ℝ) = 2 * log (sqrt (q:ℝ)) := by rw [log_sqrt hq0.le]; ring
  set s := sqrt (q:ℝ) with hs
  set L := log (q:ℝ) with hLdef
  have hs0 : 0 < s := by linarith
  have hl2 := log_two_lt_d9
  have hlogs : log s ≤ s / 16 - 1 + 4 * log 2 := by
    have h := log_le_sub_one_of_pos (show 0 < s / 16 by positivity)
    rw [log_div hs0.ne' (by norm_num), show (16:ℝ) = 2 ^ 4 by norm_num, log_pow] at h
    push_cast at h; linarith
  have hpi := pi_gt_d2
  have hc : 4 / π ≤ 1.2739 := by rw [div_le_iff₀ pi_pos]; nlinarith
  have hL0 : 0 ≤ L := log_nonneg (by linarith)
  set x := 4 / π * s * L with hx
  have hHx : (⌊x⌋₊:ℝ) ≤ x := Nat.floor_le (by positivity)
  have hLb : L ≤ s / 8 + 3.5453 := by linarith
  have hsL : s * L ≤ s * (s / 8 + 3.5453) := mul_le_mul_of_nonneg_left hLb hs0.le
  have hxb : x ≤ 1.2739 * (s * (s / 8 + 3.5453)) := by
    rw [hx, mul_assoc]
    exact mul_le_mul hc hsL (by positivity) (by norm_num)
  have : (2:ℝ) * (⌊x⌋₊ + 1) < q := by nlinarith
  exact_mod_cast this

theorem odd_main {q : ℕ} (hq : 1000 < q) :
      1 + 4 * q / (π ^ 2 * (⌊4 / π * sqrt q * log q⌋₊ + 1)) *
          (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) ≤
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log ⌊4 / π * sqrt q * log q⌋₊ + eulerMascheroniConstant + log 2 +
            3 / ⌊4 / π * sqrt q * log q⌋₊) := by
  have hH235 := (odd_one hq).2
  have hqR : (1001:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hss : sqrt (q:ℝ) * sqrt (q:ℝ) = q := mul_self_sqrt hq0.le
  have hs31 : 31 ≤ sqrt (q:ℝ) := by
    rw [show (31:ℝ) = sqrt 961 by rw [show (961:ℝ) = 31^2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by linarith)
  have hL6 : 6 ≤ log (q:ℝ) := by
    rw [le_log_iff_exp_le hq0]; linarith [exp6_le]
  have hLs : log (q:ℝ) = 2 * log (sqrt (q:ℝ)) := by rw [log_sqrt hq0.le]; ring
  set s := sqrt (q:ℝ) with hs
  set L := log (q:ℝ) with hLdef
  have hs0 : 0 < s := by linarith
  set x := 4 / π * s * L with hx
  set H := ⌊x⌋₊ with hHdef
  have hx0 : 0 ≤ x := by positivity
  have hHx : (H:ℝ) ≤ x := Nat.floor_le hx0
  have hxH : x < H + 1 := Nat.lt_floor_add_one x
  have hl2 := log_two_lt_d9
  have hpi := pi_gt_d2
  have hγ := eulerMascheroniConstant_lt_two_thirds
  have hl4 : log (4 / π) ≤ 0.2739 := by
    have h := log_le_sub_one_of_pos (show 0 < 4 / π by positivity)
    have : 4 / π ≤ 4 / 3.14 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi.le
    linarith [show (4:ℝ) / 3.14 ≤ 1.2739 by norm_num]
  have hl4' : 0 ≤ log (4 / π) := log_nonneg (by rw [le_div_iff₀ pi_pos]; linarith [pi_lt_four])
  have htiny : π ^ 2 / (12 * (q:ℝ) ^ 2) ≤ 0.001 := by
    have hp16 : π ^ 2 ≤ 16 := by nlinarith [pi_lt_four, pi_pos]
    have hq2 : (6561:ℝ) ≤ (q:ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]; linarith
  have htiny' : 0 ≤ π ^ 2 / (12 * (q:ℝ) ^ 2) := by positivity
  set Lq := L + log (4 / π) + π ^ 2 / (12 * (q:ℝ) ^ 2) with hLq
  set K := s / π with hK
  have hK0 : 0 < K := by positivity
  have hKs : K ≤ 0.3185 * s := by
    rw [hK, div_le_iff₀ pi_pos]; nlinarith
  have hA : 4 * (q:ℝ) / (π ^ 2 * (H + 1)) ≤ K / L := by
    have key : s * π * x < s * π * (H + 1) := mul_lt_mul_of_pos_left hxH (by positivity)
    have ex : s * π * x = 4 * q * L := by
      rw [hx, ← hss]; field_simp
    have eK : K * (π ^ 2 * (H + 1)) = s * π * (H + 1) := by
      rw [hK]; field_simp
    rw [div_le_div_iff₀ (by positivity) (by linarith), eK]; linarith
  have hLq0 : 0 ≤ Lq := by positivity
  have hALq : 4 * (q:ℝ) / (π ^ 2 * (H + 1)) * Lq ≤ K * 1.0459 := by
    calc _ ≤ K / L * Lq := mul_le_mul_of_nonneg_right hA hLq0
      _ = K * (Lq / L) := by ring
      _ ≤ K * 1.0459 := by
        apply mul_le_mul_of_nonneg_left _ hK0.le
        rw [div_le_iff₀ (by linarith)]; linarith
  have hlogH : log (H:ℝ) ≤ log (4 / π) + L / 2 + log L := by
    have h := log_le_log (by linarith) hHx
    rw [hx, log_mul (by positivity) (by linarith), log_mul (by positivity) hs0.ne'] at h
    linarith
  have h1 : K * log (H:ℝ) ≤ K * (log (4 / π) + L / 2 + log L) :=
    mul_le_mul_of_nonneg_left hlogH hK0.le
  have h1' : K * log (4 / π) ≤ K * 0.2739 := mul_le_mul_of_nonneg_left hl4 hK0.le
  have h2 : K * eulerMascheroniConstant ≤ K * (2 / 3) := mul_le_mul_of_nonneg_left hγ.le hK0.le
  have h3 : K * log 2 ≤ K * 0.6932 := mul_le_mul_of_nonneg_left (by linarith) hK0.le
  have h4 : K * (3 / (H:ℝ)) ≤ K * (3 / 235) := by
    apply mul_le_mul_of_nonneg_left _ hK0.le
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH235.le
  have hKL : 1 / (2 * π) * s * L = K * L / 2 := by rw [hK]; ring
  have hKL2 : 1 / π * s * log L = K * log L := by rw [hK]; ring
  rw [hKL, hKL2]
  have e : K * (log (H:ℝ) + eulerMascheroniConstant + log 2 + 3 / (H:ℝ)) =
    K * log (H:ℝ) + K * eulerMascheroniConstant + K * log 2 + K * (3 / (H:ℝ)) := by ring
  rw [e]
  have e2 : K * (log (4 / π) + L / 2 + log L) = K * log (4 / π) + K * L / 2 + K * log L := by ring
  linarith

theorem odd_close_proof {q : ℕ} (hq : 1000 < q) :
    1 ≤ ⌊4 / π * sqrt q * log q⌋₊ ∧ 2 * (⌊4 / π * sqrt q * log q⌋₊ + 1) < q ∧
      1 + 4 * q / (π ^ 2 * (⌊4 / π * sqrt q * log q⌋₊ + 1)) *
          (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) ≤
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log ⌊4 / π * sqrt q * log q⌋₊ + eulerMascheroniConstant + log 2 +
            3 / ⌊4 / π * sqrt q * log q⌋₊) :=
  ⟨(odd_one hq).1, odd_two hq, odd_main hq⟩

end LeanLab.HelfgottMajor.PVOddLarge1122Aux.Close

namespace LeanLab.HelfgottMajor.PVOddLarge1122

open Real Finset

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 4, the bound for C_n on page 9, in cotangent form: for χ odd
the terms h and q - h of the head pair to cot(πm/q) times a cosine difference, as in
`PVOddFold1122.cot_sum_fold` restricted to m ≤ H. Class MEDIUM. -/
theorem odd_head_fold {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (H : ℕ) (hH : 1 ≤ H) (hHq : 2 * H < q) (M N : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val),
        χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ ≤
      2 * ∑ m ∈ Icc 1 H,
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  apply odd_head_fold_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 4, the bound for D_n on page 9, "estimated as with B_n", the
entry of Lemma 4: by `PVTailAbel1122.dual_bound` with w(h) = cot(πh/q)(e(h)^(N+1) - e(h)^M),
e(h)^n e(ah) = e((a+n)h), and the shifts a ↦ a + N + 1, a ↦ a + M turn the sum over a into
twice the sum over b of the tail norms. Class MEDIUM. -/
theorem odd_tail_dual {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (H M N : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ ≤
      2 / sqrt q * ∑ b : ZMod q, ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ := by
  apply odd_tail_dual_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 4, page 10, the choice n = ⌊(4/π) q^(1/2) log q⌋ and the final
inequality: for q > 1000, 2(n+1) < q and 1 + 4q/(π²(n+1)) (log q + log(4/π) + π²/(12q²)) is at
most the remainder of `odd_truncated_large` at n. Uses log n ≤ log(4/π) + log √q + log log q,
n + 1 ≥ (4/π) √q log q and γ < 0.5773. Class MEDIUM. -/
theorem odd_close {q : ℕ} (hq : 1000 < q) :
    1 ≤ ⌊4 / π * sqrt q * log q⌋₊ ∧ 2 * (⌊4 / π * sqrt q * log q⌋₊ + 1) < q ∧
      1 + 4 * q / (π ^ 2 * (⌊4 / π * sqrt q * log q⌋₊ + 1)) *
          (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) ≤
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log ⌊4 / π * sqrt q * log q⌋₊ + eulerMascheroniConstant + log 2 +
            3 / ⌊4 / π * sqrt q * log q⌋₊) := by
  apply LeanLab.HelfgottMajor.PVOddLarge1122Aux.Close.odd_close_proof <;> assumption

/-- The head of the cotangent sum over 2√q is at most √q/π ∑_{m ≤ H} |cos mβ - cos mα|/m,
Pomerance's bound for |C_n| before Lemma 2. PROVED from the LEAF `odd_head_fold` and
`PVOddTrunc1122.cot_le`. -/
theorem head_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (H : ℕ) (hH : 1 ≤ H) (hHq : 2 * H < q) (M N : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val),
        χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ / (2 * sqrt q) ≤
      sqrt q / π * ∑ m ∈ Icc 1 H,
        |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  have h1 := odd_head_fold χ hq7 hodd H hH hHq M N
  have h2 : ∑ m ∈ Icc 1 H,
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| ≤
      ∑ m ∈ Icc 1 H, q / π *
        (|cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m) := by
    refine sum_le_sum fun m hm => ?_
    rw [mem_Icc] at hm
    have hc := LeanLab.HelfgottMajor.PVOddTrunc1122.cot_le (q := q) (h := m) hm.1 (by omega)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have ha := abs_nonneg (cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q)))
    calc Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))|
        ≤ q / (π * m) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| :=
          mul_le_mul_of_nonneg_right hc ha
      _ = q / π * (|cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m) := by
          field_simp
  rw [← mul_sum] at h2
  set S := ∑ m ∈ Icc 1 H, |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m
  rw [div_le_iff₀ (by positivity)]
  have hqs : (q : ℝ) = sqrt q * sqrt q := (mul_self_sqrt hq0.le).symm
  calc _ ≤ 2 * (q / π * S) := h1.trans (by linarith)
    _ = sqrt q / π * S * (2 * sqrt q) := by linear_combination (2 * S / π) * hqs

/-- The tail of the cotangent sum over 2√q is at most 4q/(π²(H+1)) (log q + log(4/π) +
π²/(12q²)), Pomerance's bound for |D_n|. PROVED from the LEAF `odd_tail_dual` and the
pieces of `PVTailAbel1122`. -/
theorem tail_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (H : ℕ) (hHq : 2 * (H + 1) < q) (M N : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ / (2 * sqrt q) ≤
      4 * q / (π ^ 2 * (H + 1)) * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) := by
  have hq1 : 1 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  have hd := odd_tail_dual χ hχ H M N
  have hV := LeanLab.HelfgottMajor.PVTailAbel1122.tail_V_sum (q := q) H hHq
  have hC := LeanLab.HelfgottMajor.PVTailAbel1122.csc_sum hq1
  have hy0 : 0 < π * ((H : ℝ) + 1) / q := by positivity
  have hy1 : π * ((H : ℝ) + 1) / q < π / 2 := by
    have : (2 : ℝ) * ((H : ℝ) + 1) < q := by exact_mod_cast hHq
    rw [div_lt_div_iff₀ hq0 two_pos]; nlinarith [pi_pos]
  obtain ⟨hcp, hcl⟩ := LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_pos_le_inv hy0 hy1
  have hcl' : cot (π * ((H : ℝ) + 1) / q) ≤ q / (π * ((H : ℝ) + 1)) := by
    rw [one_div_div] at hcl; exact hcl
  set Lq := log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)
  set C := ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q)
  have hC0 : 0 ≤ C := by
    refine sum_nonneg fun a ha => ?_
    rw [mem_Icc] at ha
    have : 0 < sin (π * a / q) := by
      apply sin_pos_of_pos_of_lt_pi
      · have : (1:ℝ) ≤ a := by exact_mod_cast ha.1
        positivity
      · have : (a : ℝ) < q := by exact_mod_cast (show a < q by omega)
        rw [div_lt_iff₀ hq0]; nlinarith [pi_pos]
    positivity
  set T := ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖
  have h1 : T ≤ 2 / sqrt q * (2 * (q / (π * ((H : ℝ) + 1))) * (2 * q / π * Lq)) := by
    refine hd.trans (mul_le_mul_of_nonneg_left (hV.trans ?_) (by positivity))
    have : 2 * cot (π * ((H : ℝ) + 1) / q) * C ≤ 2 * (q / (π * ((H : ℝ) + 1))) * C :=
      mul_le_mul_of_nonneg_right (by linarith) hC0
    refine this.trans (mul_le_mul_of_nonneg_left hC.le (by positivity))
  rw [div_le_iff₀ (by positivity)]
  have hqs : (q : ℝ) = sqrt q * sqrt q := (mul_self_sqrt hq0.le).symm
  calc T ≤ 2 / sqrt q * (2 * (q / (π * ((H : ℝ) + 1))) * (2 * q / π * Lq)) := h1
    _ = 4 * q / (π ^ 2 * ((H : ℝ) + 1)) * Lq * (2 * sqrt q) := by
      field_simp
      rw [sq_sqrt hq0.le]; ring

/-- From the PROVED identity `PVOddCot1122.polya_interval_cot` and |τ(χ⁻¹)| = √q:
‖S‖ ≤ 1 + ‖W‖/(2√q), Pomerance page 9, the terms χ(M)/2 + χ(N)/2. PROVED. -/
theorem interval_le_cot_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) {M N : ℕ} (hMN : M ≤ N + 1) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 + ‖∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ / (2 * sqrt q) := by
  have hid := LeanLab.HelfgottMajor.PVOddCot1122.polya_interval_cot hχ hq hMN
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  have hg := LeanLab.HelfgottMajor.PVEvenTrunc1122.norm_gauss_inv hχ
  set S := ∑ m ∈ Icc M N, χ (m : ZMod q)
  set W := ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)
  set G := gaussSum χ⁻¹ ZMod.stdAddChar
  have hn := congrArg norm hid
  rw [norm_mul, hg] at hn
  have hc : ‖χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have := DirichletCharacter.norm_le_one χ ((N + 1 : ℕ) : ZMod q)
    have := DirichletCharacter.norm_le_one χ (M : ZMod q)
    linarith
  have htri : ‖-(1 / 2) * G * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q)) - Complex.I / 2 * W‖ ≤
      1 / 2 * sqrt q * 2 + 1 / 2 * ‖W‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, hg]
      have : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    · rw [norm_mul]
      have : ‖Complex.I / 2‖ = 1 / 2 := by simp
      rw [this]
  rw [← hn] at htri
  rw [div_eq_mul_inv, mul_inv]
  have hsq : sqrt (q : ℝ) * ‖S‖ ≤ sqrt q * (1 + ‖W‖ * (2⁻¹ * (sqrt q)⁻¹)) := by
    have : sqrt q * (1 + ‖W‖ * (2⁻¹ * (sqrt q)⁻¹)) = 1 / 2 * sqrt q * 2 + 1 / 2 * ‖W‖ := by
      field_simp
    rw [this]; exact htri
  exact le_of_mul_le_mul_left hsq hs

/-- Assembly: exactly the LEAF `PVOddTrunc1122.odd_truncated_large`. PROVED from the LEAFs
above and those of `PVTailAbel1122`. -/
theorem odd_truncated_large {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 1000 < q) (hodd : χ (-1) ≠ 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  obtain ⟨hH1, hHq, hcl⟩ := odd_close hq
  set H := ⌊4 / π * sqrt q * log q⌋₊ with hHdef
  refine ⟨H, hH1, fun M N => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  set Lq := log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)
  have hLq : 0 ≤ 4 * q / (π ^ 2 * ((H : ℝ) + 1)) * Lq := by
    have : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have : 0 ≤ log (4 / π) := log_nonneg (by rw [le_div_iff₀ pi_pos]; linarith [pi_lt_four])
    positivity
  have hhead0 : 0 ≤ sqrt q / π * ∑ m ∈ Icc 1 H,
      |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m := by
    refine mul_nonneg (by positivity) (sum_nonneg fun m _ => by positivity)
  by_cases hMN : M ≤ N + 1
  · have h1 := interval_le_cot_sum χ hχ (by omega) hMN
    set f : ZMod q → ℂ := fun h => χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
          (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)
    have hsplit := (sum_filter_add_sum_filter_not univ
      (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val) f)
    have htri := norm_add_le (∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), f h)
      (∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), f h)
    rw [hsplit] at htri
    have hd : 0 < 2 * sqrt (q : ℝ) := by positivity
    have hdiv := div_le_div_of_nonneg_right htri hd.le
    rw [add_div] at hdiv
    have hh := head_bound χ (by omega) hodd H hH1 (by omega) M N
    have ht := tail_bound χ hχ H hHq M N
    linarith
  · have hE : Icc M N = ∅ := by
      ext m; simp only [mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [hE, sum_empty, norm_zero]
    linarith

example : type_of% @odd_truncated_large =
    type_of% @LeanLab.HelfgottMajor.PVOddTrunc1122.odd_truncated_large := rfl

end LeanLab.HelfgottMajor.PVOddLarge1122

#print axioms LeanLab.HelfgottMajor.PVOddLarge1122.odd_head_fold
#print axioms LeanLab.HelfgottMajor.PVOddLarge1122.odd_tail_dual
#print axioms LeanLab.HelfgottMajor.PVOddLarge1122.odd_close
#print axioms LeanLab.HelfgottMajor.PVOddLarge1122.head_bound
#print axioms LeanLab.HelfgottMajor.PVOddLarge1122.tail_bound
#print axioms LeanLab.HelfgottMajor.PVOddLarge1122.interval_le_cot_sum
#print axioms LeanLab.HelfgottMajor.PVOddLarge1122.odd_truncated_large
