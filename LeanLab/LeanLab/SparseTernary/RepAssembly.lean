/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Sections 4.2, 5, 6, display (4.14).
The circle method assembly: `RepProp A` from a minor arc upper bound and a major arc lower bound.

What is proved here, with zero sorry:
* `circle_split`: `𝔑(m) = ∫_𝔐 S³e(-mα) + ∫_{𝔪'} S³e(-mα)`, where `𝔪'` is the minor arc set
  taken inside the unit window `(1/Q, 1 + 1/Q]`, valid whenever `0 < P` and `2P < Q`.
  The paper's (4.14) uses `𝔪 = [0,1] \ 𝔐`; then `𝔐 ∪ 𝔪 ≠ [0,1]` since the arc at `1/1`
  reaches `1 + 1/Q`, and `[0, 1/Q]`, where `S` is as large as at `α = 1`, sits inside `𝔪`.
  So `Minor516W` below replaces `Section4.Minor516` by the same bound over `𝔪'`.
* `Rfrak_le_of_not`: if `m` is NOT a sum of three primes of `P_u`, then the von Mangoldt
  weighted count `𝔑(m)`, which also counts prime powers, is at most
  `log(2u)³ · 3 · #{proper prime powers ≤ 2u} · (2u + 1)`, which is `O(u^{3/2} (log u)⁴)`.
* `pp_small`: that bound is eventually below `u² / (2 (log u)^κ)`, for every real `κ`.
* `repProp_of_parts`: `RepProp A`, CONDITIONAL ON `Minor516W A B` and `MajorLower A B κ`
  with `κ < B/2 - 5A - 5`, nothing else.

AI-written Lean code, Claude, run 20261021T0103Z-19411, unit U-1314. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Section4
import LeanLab.SparseTernary.Identity412

open Finset Filter Real Asymptotics MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.RepAssembly

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4

/-! ### The integrand, periodicity, measurability -/

/-- The integrand `S(α)³ e(-mα)` of (4.12). -/
def F (Z : ℕ) (u : ℝ) (m : ℕ) (α : ℝ) : ℂ := Sexp Z u α ^ 3 * ee (-(m * α))

theorem ee_shift (x : ℝ) (n : ℤ) : ee (x + n) = ee x := by
  have h : ee (x + n) = ee x * Complex.exp (n * (2 * Real.pi * Complex.I)) := by
    unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem F_periodic (Z : ℕ) (u : ℝ) (m : ℕ) : Function.Periodic (F Z u m) 1 := by
  intro α
  have h1 : ∀ k : ℕ, ee (k * (α + 1)) = ee (k * α) := fun k => by
    rw [← ee_shift (k * α) (k : ℤ)]; congr 1; push_cast; ring
  have h2 : ee (-(m * (α + 1))) = ee (-(m * α)) := by
    rw [← ee_shift (-(m * α)) (-(m : ℤ))]; congr 1; push_cast; ring
  unfold F Sexp; rw [h2]; simp only [h1]

theorem continuous_F (Z : ℕ) (u : ℝ) (m : ℕ) : Continuous (F Z u m) := by
  have hS : Continuous (fun α => Sexp Z u α) := by
    unfold Sexp
    exact continuous_finsetSum _ fun k _ =>
      continuous_const.mul (Identity.continuous_ee.comp (continuous_const.mul continuous_id))
  unfold F
  exact (hS.pow 3).mul (Identity.continuous_ee.comp (continuous_const.mul continuous_id).neg)

theorem measurableSet_majorArcs (P Q : ℝ) : MeasurableSet (majorArcs P Q) := by
  have e : majorArcs P Q = ⋃ q : ℕ, ⋃ a : ℕ, {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧
      a.Coprime q ∧ |α - a / q| ≤ 1 / Q} := by
    ext α; simp only [majorArcs, Set.mem_setOf_eq, Set.mem_iUnion]; constructor
    · rintro ⟨q, h1, h2, a, h3, h4, h5, h6⟩; exact ⟨q, a, h1, h2, h3, h4, h5, h6⟩
    · rintro ⟨q, a, h1, h2, h3, h4, h5, h6⟩; exact ⟨q, h1, h2, a, h3, h4, h5, h6⟩
  rw [e]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases hc : 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧ a.Coprime q
  · have e2 : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧ a.Coprime q ∧
        |α - a / q| ≤ 1 / Q} = {α : ℝ | |α - a / q| ≤ 1 / Q} := by
      ext α; simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h.2.2.2.2.2, fun h => ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, h⟩⟩
    rw [e2]
    exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
  · have e2 : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧ a.Coprime q ∧
        |α - a / q| ≤ 1 / Q} = ∅ := by
      ext α; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hc ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    rw [e2]; exact MeasurableSet.empty

/-! ### The unit window and the corrected minor arcs -/

/-- The unit window `(1/Q, 1 + 1/Q]`, one full period of `F`. -/
def window (Q : ℝ) : Set ℝ := Set.Ioc (1 / Q) (1 / Q + 1)

/-- Minor arcs inside the window: `𝔪' = (1/Q, 1 + 1/Q] \ 𝔐`. The paper writes
`𝔪 = [0,1] \ 𝔐`, which differs from `𝔪'` by `[0, 1/Q]` and so does not complement `𝔐`. -/
def minorArcsW (P Q : ℝ) : Set ℝ := window Q \ majorArcs P Q

/-- For `0 < P` and `2P < Q`, every major arc lies in the window. -/
theorem majorArcs_sub_window {P Q : ℝ} (hP : 0 < P) (hPQ : 2 * P < Q) :
    majorArcs P Q ⊆ window Q := by
  rintro α ⟨q, hq1, hqP, a, ha1, haq, -, hα⟩
  have hQ : 0 < Q := by linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast hq1
  have haq' : (a : ℝ) / q ≤ 1 := by rw [div_le_one hq]; exact_mod_cast haq
  have ha' : 1 / P ≤ (a : ℝ) / q := by
    calc 1 / P ≤ 1 / q := one_div_le_one_div_of_le hq hqP
      _ ≤ a / q := div_le_div_of_nonneg_right (by exact_mod_cast ha1) hq.le
  have h2 : 2 * (1 / Q) < 1 / P := by
    rw [show 2 * (1 / Q) = 2 / Q by ring, div_lt_div_iff₀ hQ hP]; linarith
  rw [abs_le] at hα
  exact Set.mem_Ioc.mpr ⟨by linarith [hα.1], by linarith [hα.2]⟩

/-- **(4.14), corrected**: for `0 < P`, `2P < Q`, the count `𝔑(m)` is the major arc
integral plus the integral over `𝔪'`. Uses `Identity.identity412` and periodicity. -/
theorem circle_split (Z : ℕ) (u : ℝ) (m : ℕ) {P Q : ℝ} (hP : 0 < P) (hPQ : 2 * P < Q) :
    ((Rfrak Z u m : ℝ) : ℂ) =
      (∫ α in majorArcs P Q, Sexp Z u α ^ 3 * ee (-(m * α))) +
        ∫ α in minorArcsW P Q, Sexp Z u α ^ 3 * ee (-(m * α)) := by
  have hQ : 0 < Q := by linarith
  rw [Identity.identity412 Z u m]
  have e2 := (F_periodic Z u m).intervalIntegral_add_eq 0 (1 / Q)
  rw [zero_add] at e2
  have e3 : ∫ x in (1 / Q)..(1 / Q + 1), F Z u m x = ∫ x in window Q, F Z u m x :=
    intervalIntegral.integral_of_le (by linarith)
  have hint : IntegrableOn (F Z u m) (window Q) :=
    (continuous_F Z u m).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsplit := integral_inter_add_sdiff (measurableSet_majorArcs P Q) hint
  rw [Set.inter_eq_right.mpr (majorArcs_sub_window hP hPQ)] at hsplit
  calc ∫ α in (0 : ℝ)..1, Sexp Z u α ^ 3 * ee (-(m * α)) = ∫ α in (0 : ℝ)..1, F Z u m α := rfl
    _ = ∫ α in (1 / Q)..(1 / Q + 1), F Z u m α := e2
    _ = ∫ x in window Q, F Z u m x := e3
    _ = _ := hsplit.symm

/-- Real part bookkeeping: `R = I + J` gives `Re I - ‖J‖ ≤ R`. -/
theorem lower_of_split {R : ℝ} {I J : ℂ} (h : (R : ℂ) = I + J) : I.re - ‖J‖ ≤ R := by
  have h1 : R = I.re + J.re := by simpa using congrArg Complex.re h
  have h2 : -‖J‖ ≤ J.re := by
    have := Complex.abs_re_le_norm J; linarith [neg_abs_le J.re]
  linarith

/-! ### Prime powers: from a positive weighted count to three primes -/

/-- Proper prime powers in `[1, n]`: `Λ(k) ≠ 0` but `k` not prime. -/
def NP (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun k => IsPrimePow k ∧ ¬ k.Prime)

theorem NP_sub (n : ℕ) :
    NP n ⊆ ((Icc 1 n.sqrt) ×ˢ (Icc 2 (Nat.log 2 n))).image (fun x => x.1 ^ x.2) := by
  intro k hk
  simp only [NP, mem_filter, mem_Icc] at hk
  obtain ⟨⟨-, hkn⟩, hpp, hnp⟩ := hk
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hj2 : 2 ≤ j := by
    by_contra h
    have h1 : j = 1 := by omega
    subst h1; exact hnp (by rw [pow_one]; exact hp)
  simp only [mem_image, mem_product, mem_Icc, Prod.exists]
  refine ⟨p, j, ⟨⟨hp.one_lt.le, ?_⟩, hj2, ?_⟩, rfl⟩
  · rw [Nat.le_sqrt']
    exact (Nat.pow_le_pow_right hp.pos hj2).trans hkn
  · exact Nat.le_log_of_pow_le (by norm_num) ((Nat.pow_le_pow_left hp.two_le j).trans hkn)

theorem card_NP_le (n : ℕ) : #(NP n) ≤ n.sqrt * Nat.log 2 n := by
  refine (card_le_card (NP_sub n)).trans (card_image_le.trans ?_)
  rw [card_product, Nat.card_Icc, Nat.card_Icc]
  exact Nat.mul_le_mul (by omega) (by omega)

theorem mem_Aset_bounds {Z : ℕ} {u : ℝ} (hu : 1 ≤ u) {k : ℕ} (hk : k ∈ Aset Z u) :
    1 ≤ k ∧ k ≤ ⌊2 * u⌋₊ ∧ (k : ℝ) ≤ 2 * u := by
  simp only [Aset, mem_filter, mem_Icc] at hk
  have h0 : 0 < ⌈u⌉₊ := Nat.ceil_pos.mpr (by linarith)
  exact ⟨by omega, hk.1.2, (Nat.cast_le.mpr hk.1.2).trans (Nat.floor_le (by linarith))⟩

theorem card_Aset_le (Z : ℕ) (u : ℝ) : #(Aset Z u) ≤ ⌊2 * u⌋₊ + 1 := by
  unfold Aset
  refine (card_filter_le _ _).trans ?_
  rw [Nat.card_Icc]; omega

theorem vM_le {Z : ℕ} {u : ℝ} (hu : 1 ≤ u) {k : ℕ} (hk : k ∈ Aset Z u) :
    ArithmeticFunction.vonMangoldt k ≤ Real.log (2 * u) := by
  obtain ⟨h1, -, h3⟩ := mem_Aset_bounds hu hk
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (Nat.cast_pos.mpr (by omega)) h3)

theorem mem_Pu_of {Z : ℕ} {u : ℝ} {k : ℕ} (hk : k ∈ Aset Z u) (hp : k.Prime) : k ∈ Pu Z u := by
  simp only [Aset, Pu, mem_filter] at hk ⊢; exact ⟨hk.1, hp, hk.2⟩

theorem mem_NP_of {Z : ℕ} {u : ℝ} (hu : 1 ≤ u) {k : ℕ} (hk : k ∈ Aset Z u)
    (hpp : IsPrimePow k) (hnp : ¬ k.Prime) : k ∈ NP ⌊2 * u⌋₊ := by
  obtain ⟨h1, h2, -⟩ := mem_Aset_bounds hu hk
  simp only [NP, mem_filter, mem_Icc]; exact ⟨⟨h1, h2⟩, hpp, hnp⟩

/-- The triples of (4.11). -/
def T (Z : ℕ) (u : ℝ) (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Aset Z u ×ˢ Aset Z u ×ˢ Aset Z u).filter (fun t => t.1 + t.2.1 + t.2.2 = m)

/-- The weight `Λ(k₁)Λ(k₂)Λ(k₃)`. -/
def wt (t : ℕ × ℕ × ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt t.1 * ArithmeticFunction.vonMangoldt t.2.1 *
    ArithmeticFunction.vonMangoldt t.2.2

theorem Rfrak_eq_T (Z : ℕ) (u : ℝ) (m : ℕ) : Rfrak Z u m = ∑ t ∈ T Z u m, wt t := by
  unfold Rfrak T wt
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [sum_product]

/-- A triple with one coordinate in `N` is fixed by that coordinate and one other one. -/
theorem card_filter_T (A N : Finset ℕ) (m : ℕ) (i j : ℕ × ℕ × ℕ → ℕ)
    (hinj : ∀ t s : ℕ × ℕ × ℕ, t.1 + t.2.1 + t.2.2 = m → s.1 + s.2.1 + s.2.2 = m →
      i t = i s → j t = j s → t = s)
    (hj : ∀ t ∈ A ×ˢ A ×ˢ A, j t ∈ A) :
    #(((A ×ˢ A ×ˢ A).filter (fun t => t.1 + t.2.1 + t.2.2 = m)).filter (fun t => i t ∈ N))
      ≤ #N * #A := by
  rw [← card_product]
  refine card_le_card_of_injOn (fun t => (i t, j t)) ?_ ?_
  · intro t ht
    rw [mem_coe] at ht ⊢
    simp only [mem_filter] at ht
    exact mem_product.mpr ⟨ht.2, hj t ht.1.1⟩
  · intro t ht s hs h
    rw [mem_coe] at ht hs
    simp only [mem_filter] at ht hs
    simp only [Prod.mk.injEq] at h
    exact hinj t s ht.1.2 hs.1.2 h.1 h.2

/-- Some coordinate of the triple is a proper prime power. -/
def Cnp (n : ℕ) (t : ℕ × ℕ × ℕ) : Prop := t.1 ∈ NP n ∨ t.2.1 ∈ NP n ∨ t.2.2 ∈ NP n

/-- **Prime powers are negligible, finite form**: if `m` is not a sum of three primes of
`P_u`, then `𝔑(m) ≤ log(2u)³ · 3 · #NP(⌊2u⌋) · (⌊2u⌋ + 1)`. -/
theorem Rfrak_le_of_not (Z : ℕ) (u : ℝ) (hu : 1 ≤ u) (m : ℕ)
    (hno : ¬ IsSum3In (↑(Pu Z u) : Set ℕ) m) :
    Rfrak Z u m ≤
      Real.log (2 * u) ^ 3 * (3 * ((#(NP ⌊2 * u⌋₊) * (⌊2 * u⌋₊ + 1) : ℕ) : ℝ)) := by
  rw [Rfrak_eq_T]
  have hℓ : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith)
  have key : ∀ t ∈ T Z u m, wt t ≤
      if Cnp ⌊2 * u⌋₊ t then Real.log (2 * u) ^ 3 else 0 := by
    intro t ht
    simp only [T, mem_filter, mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, hs⟩ := ht
    have n1 := ArithmeticFunction.vonMangoldt_nonneg (n := t.1)
    have n2 := ArithmeticFunction.vonMangoldt_nonneg (n := t.2.1)
    have n3 := ArithmeticFunction.vonMangoldt_nonneg (n := t.2.2)
    split_ifs with hc
    · unfold wt
      calc _ ≤ Real.log (2 * u) * Real.log (2 * u) * Real.log (2 * u) :=
            mul_le_mul (mul_le_mul (vM_le hu h1) (vM_le hu h2) n2 hℓ) (vM_le hu h3) n3
              (mul_nonneg hℓ hℓ)
        _ = _ := by ring
    · simp only [Cnp, not_or] at hc
      obtain ⟨c1, c2, c3⟩ := hc
      have pr : ∀ k ∈ Aset Z u, k ∉ NP ⌊2 * u⌋₊ → ArithmeticFunction.vonMangoldt k ≠ 0 →
          k.Prime := by
        intro k hk hn hv
        by_contra hnp
        exact hn (mem_NP_of hu hk (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hv) hnp)
      unfold wt
      by_cases v1 : ArithmeticFunction.vonMangoldt t.1 = 0
      · rw [v1]; simp
      by_cases v2 : ArithmeticFunction.vonMangoldt t.2.1 = 0
      · rw [v2]; simp
      by_cases v3 : ArithmeticFunction.vonMangoldt t.2.2 = 0
      · rw [v3]; simp
      exact (hno ⟨t.1, t.2.1, t.2.2, mem_Pu_of h1 (pr _ h1 c1 v1),
        mem_Pu_of h2 (pr _ h2 c2 v2), mem_Pu_of h3 (pr _ h3 c3 v3), hs⟩).elim
  have hsub : (T Z u m).filter (Cnp ⌊2 * u⌋₊) ⊆
      ((T Z u m).filter (fun t => t.1 ∈ NP ⌊2 * u⌋₊) ∪
        (T Z u m).filter (fun t => t.2.1 ∈ NP ⌊2 * u⌋₊)) ∪
        (T Z u m).filter (fun t => t.2.2 ∈ NP ⌊2 * u⌋₊) := by
    intro t ht; simp only [Cnp, mem_filter, mem_union] at ht ⊢; tauto
  have hA1 : ∀ t ∈ Aset Z u ×ˢ Aset Z u ×ˢ Aset Z u, t.1 ∈ Aset Z u :=
    fun t ht => (mem_product.mp ht).1
  have hA2 : ∀ t ∈ Aset Z u ×ˢ Aset Z u ×ˢ Aset Z u, t.2.1 ∈ Aset Z u :=
    fun t ht => (mem_product.mp (mem_product.mp ht).2).1
  have c1 : #((T Z u m).filter (fun t => t.1 ∈ NP ⌊2 * u⌋₊)) ≤
      #(NP ⌊2 * u⌋₊) * #(Aset Z u) :=
    card_filter_T (Aset Z u) (NP ⌊2 * u⌋₊) m (fun t => t.1) (fun t => t.2.1)
      (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h1 h2 h3 h4; simp only at h1 h2 h3 h4
          simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> omega) hA2
  have c2 : #((T Z u m).filter (fun t => t.2.1 ∈ NP ⌊2 * u⌋₊)) ≤
      #(NP ⌊2 * u⌋₊) * #(Aset Z u) :=
    card_filter_T (Aset Z u) (NP ⌊2 * u⌋₊) m (fun t => t.2.1) (fun t => t.1)
      (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h1 h2 h3 h4; simp only at h1 h2 h3 h4
          simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> omega) hA1
  have c3 : #((T Z u m).filter (fun t => t.2.2 ∈ NP ⌊2 * u⌋₊)) ≤
      #(NP ⌊2 * u⌋₊) * #(Aset Z u) :=
    card_filter_T (Aset Z u) (NP ⌊2 * u⌋₊) m (fun t => t.2.2) (fun t => t.1)
      (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h1 h2 h3 h4; simp only at h1 h2 h3 h4
          simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> omega) hA1
  have hU : #((T Z u m).filter (Cnp ⌊2 * u⌋₊)) ≤
      #((T Z u m).filter (fun t => t.1 ∈ NP ⌊2 * u⌋₊)) +
        #((T Z u m).filter (fun t => t.2.1 ∈ NP ⌊2 * u⌋₊)) +
        #((T Z u m).filter (fun t => t.2.2 ∈ NP ⌊2 * u⌋₊)) :=
    (card_le_card hsub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  have hAc := Nat.mul_le_mul_left #(NP ⌊2 * u⌋₊) (card_Aset_le Z u)
  have hcard : #((T Z u m).filter (Cnp ⌊2 * u⌋₊)) ≤
      3 * (#(NP ⌊2 * u⌋₊) * (⌊2 * u⌋₊ + 1)) :=
    calc #((T Z u m).filter (Cnp ⌊2 * u⌋₊))
        ≤ #(NP ⌊2 * u⌋₊) * #(Aset Z u) + #(NP ⌊2 * u⌋₊) * #(Aset Z u) +
          #(NP ⌊2 * u⌋₊) * #(Aset Z u) := hU.trans (Nat.add_le_add (Nat.add_le_add c1 c2) c3)
      _ = 3 * (#(NP ⌊2 * u⌋₊) * #(Aset Z u)) := by ring
      _ ≤ 3 * (#(NP ⌊2 * u⌋₊) * (⌊2 * u⌋₊ + 1)) := Nat.mul_le_mul_left 3 hAc
  calc ∑ t ∈ T Z u m, wt t
      ≤ ∑ t ∈ T Z u m, (if Cnp ⌊2 * u⌋₊ t then Real.log (2 * u) ^ 3 else 0) := sum_le_sum key
    _ = Real.log (2 * u) ^ 3 * (#((T Z u m).filter (Cnp ⌊2 * u⌋₊)) : ℝ) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
        gcongr
        exact_mod_cast hcard

/-! ### The analytic bookkeeping -/

/-- For large `u`, `0 < P` and `2P < Q`, with `P = (log u)^B`, `Q = u/(log u)^B`. -/
theorem arcs_ok (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, 0 < Real.log u ^ B ∧ 2 * Real.log u ^ B < u / Real.log u ^ B := by
  have h := (isLittleO_pow_log_id_atTop (n := 2 * B)).bound (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with u hu hu1
  have hL : 0 < Real.log u := Real.log_pos hu1
  have hLB : 0 < Real.log u ^ B := pow_pos hL B
  refine ⟨hLB, ?_⟩
  rw [lt_div_iff₀ hLB]
  have h1 : Real.log u ^ (2 * B) ≤ 1 / 4 * u := by
    have h' := hu
    simp only [Real.norm_eq_abs, id_eq] at h'
    rw [abs_of_pos (by linarith : (0 : ℝ) < u)] at h'
    exact (le_abs_self _).trans h'
  calc 2 * Real.log u ^ B * Real.log u ^ B = 2 * Real.log u ^ (2 * B) := by ring
    _ ≤ 2 * (1 / 4 * u) := by linarith
    _ < u := by linarith

/-- A loss `C u²/(log u)^{κ+δ}` with `δ > 0` is eventually at most half of `u²/(log u)^κ`. -/
theorem absorb (C κ δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, C * u ^ 2 / Real.log u ^ (κ + δ) ≤ u ^ 2 / (2 * Real.log u ^ κ) := by
  have ht := (tendsto_rpow_atTop hδ).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually_ge_atTop (2 * C), eventually_gt_atTop (1 : ℝ)] with u h1 h2
  simp only [Function.comp] at h1
  have hL : 0 < Real.log u := Real.log_pos h2
  have hD : 0 < Real.log u ^ κ := Real.rpow_pos_of_pos hL _
  have hE : 0 < Real.log u ^ δ := Real.rpow_pos_of_pos hL _
  rw [Real.rpow_add hL, div_le_div_iff₀ (mul_pos hD hE) (mul_pos two_pos hD)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg u)) hD.le]

/-- **Prime powers are negligible, asymptotic form**: for every real `κ`, eventually
`log(2u)³ · 3 · #NP(⌊2u⌋) · (⌊2u⌋ + 1) < u² / (2 (log u)^κ)`. -/
theorem pp_small (κ : ℝ) : ∀ᶠ u : ℝ in atTop,
    Real.log (2 * u) ^ 3 * (3 * ((#(NP ⌊2 * u⌋₊) * (⌊2 * u⌋₊ + 1) : ℕ) : ℝ)) <
      u ^ 2 / (2 * Real.log u ^ κ) := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (4 + κ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 2000)
  filter_upwards [h1, eventually_ge_atTop (4 : ℝ)] with u hu hu4
  have hu0 : 0 < u := by linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) (by linarith)
  have hL : 0 < Real.log u := by linarith
  have hℓ : Real.log (2 * u) = Real.log 2 + Real.log u := Real.log_mul (by norm_num) hu0.ne'
  have hD : 0 < Real.log u ^ κ := Real.rpow_pos_of_pos hL _
  have hK : Real.log u ^ 4 * Real.log u ^ κ ≤ Real.sqrt u / 2000 := by
    have h' := hu
    simp only [Real.norm_eq_abs] at h'
    rw [abs_of_pos (Real.rpow_pos_of_pos hL _), abs_of_pos (Real.rpow_pos_of_pos hu0 _),
      Real.rpow_add hL, ← Real.sqrt_eq_rpow] at h'
    have h4 : Real.log u ^ (4 : ℝ) = Real.log u ^ 4 := by
      exact_mod_cast Real.rpow_natCast (Real.log u) 4
    rw [h4] at h'
    linarith
  set L := Real.log u with hLdef
  have hℓ0 : 0 ≤ Real.log (2 * u) := by rw [hℓ]; linarith
  have hℓle : Real.log (2 * u) ≤ 2 * L := by rw [hℓ]; linarith
  set n := ⌊2 * u⌋₊ with hndef
  have hn : (n : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hn1 : 1 ≤ n := Nat.le_floor (by push_cast; linarith)
  have hsq : ((n.sqrt : ℕ) : ℝ) ≤ 2 * Real.sqrt u := by
    have h1 : ((n.sqrt : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
    have h2 := Real.sq_sqrt hu0.le
    have h3 := Real.sqrt_nonneg u
    nlinarith [Nat.cast_nonneg (α := ℝ) n.sqrt]
  have hlog : ((Nat.log 2 n : ℕ) : ℝ) ≤ 4 * L := by
    have h1 := Real.natLog_le_logb n 2
    unfold Real.logb at h1
    push_cast at h1
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hln : Real.log n ≤ Real.log (2 * u) := Real.log_le_log hn0 hn
    have hln0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hdiv : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hNP : ((#(NP n) : ℕ) : ℝ) ≤ (2 * Real.sqrt u) * (4 * L) := by
    have h' : ((#(NP n) : ℕ) : ℝ) ≤ ((n.sqrt : ℕ) : ℝ) * ((Nat.log 2 n : ℕ) : ℝ) := by
      exact_mod_cast card_NP_le n
    exact h'.trans (mul_le_mul hsq hlog (Nat.cast_nonneg _) (by positivity))
  have hn3 : (n : ℝ) + 1 ≤ 3 * u := by linarith
  rw [show (((#(NP n) * (n + 1) : ℕ)) : ℝ) = (#(NP n) : ℝ) * ((n : ℝ) + 1) by push_cast; ring]
  have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  calc Real.log (2 * u) ^ 3 * (3 * ((#(NP n) : ℝ) * ((n : ℝ) + 1)))
      ≤ (2 * L) ^ 3 * (3 * ((2 * Real.sqrt u * (4 * L)) * (3 * u))) := by
        have hb : (#(NP n) : ℝ) * ((n : ℝ) + 1) ≤ (2 * Real.sqrt u * (4 * L)) * (3 * u) :=
          mul_le_mul hNP hn3 (by positivity) (by positivity)
        have hc : Real.log (2 * u) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ hℓ0 hℓle 3
        exact mul_le_mul hc (by linarith) (by positivity) (by positivity)
    _ = 576 * L ^ 4 * (u * Real.sqrt u) := by ring
    _ < u ^ 2 / (2 * L ^ κ) := by
        rw [lt_div_iff₀ (mul_pos two_pos hD)]
        have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
        have hK' : L ^ 4 * L ^ κ * (u * Real.sqrt u) ≤ u * u / 2000 := by
          calc L ^ 4 * L ^ κ * (u * Real.sqrt u) ≤ Real.sqrt u / 2000 * (u * Real.sqrt u) :=
                mul_le_mul_of_nonneg_right hK (by positivity)
            _ = u * (Real.sqrt u * Real.sqrt u) / 2000 := by ring
            _ = u * u / 2000 := by rw [hss]
        nlinarith [hK', mul_pos hu0 hu0]

/-! ### The assembly -/

/-- (5.16) over the corrected minor arcs `𝔪' = (1/Q, 1 + 1/Q] \ 𝔐`, `P = (log u)^B`,
`Q = u (log u)^{-B}`, `z = 3A log log u`. Same bound as `Section4.Minor516`. Cited, NOT proved. -/
def Minor516W (A B : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ,
    ‖∫ α in minorArcsW (Real.log u ^ B) (u / Real.log u ^ B),
        Sexp (Zof A u) u α ^ 3 * ee (-(m * α))‖ ≤
      C * u ^ 2 / Real.log u ^ ((B : ℝ) / 2 - 5 * A - 5 - 2 * ε)

/-- **RepProp A, CONDITIONAL ON `Minor516W A B` and `MajorLower A B κ`**, for any `κ` below
`B/2 - 5A - 5`. The paper's assembly (4.12), (4.14), (5.16), with the minor arcs read in the
unit window and the prime power part of `𝔑(m)` bounded here unconditionally. -/
theorem repProp_of_parts (A B : ℕ) (κ : ℝ) (hκ : κ < (B : ℝ) / 2 - 5 * A - 5)
    (hmin : Minor516W A B) (hmaj : MajorLower A B κ) : RepProp A := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = ((B : ℝ) / 2 - 5 * A - 5 - κ) / 4 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; linarith
  have he : (B : ℝ) / 2 - 5 * A - 5 - 2 * ε = κ + 2 * ε := by rw [hεdef]; ring
  obtain ⟨C, u0, hC⟩ := hmin ε hε
  obtain ⟨u1, hM⟩ := hmaj
  have hev := (arcs_ok B).and ((absorb C κ (2 * ε) (by linarith)).and
    ((pp_small κ).and (eventually_ge_atTop (max (max u0 u1) 4))))
  obtain ⟨u2, hu2⟩ := Filter.eventually_atTop.mp hev
  refine ⟨u2, fun u hu m hodd h4 h5 => ?_⟩
  obtain ⟨⟨hP, hPQ⟩, hab, hpp, hmax⟩ := hu2 u hu
  have hu0' : u0 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  have hu1' : u1 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have hu4 : 4 ≤ u := le_trans (le_max_right _ _) hmax
  by_contra hno
  have hup := Rfrak_le_of_not (Zof A u) u (by linarith) m hno
  have hlow := lower_of_split (circle_split (Zof A u) u m hP hPQ)
  have hmaj' := hM u hu1' m hodd h4 h5
  have hmin' := hC u hu0' m
  rw [he] at hmin'
  have hD : 0 < Real.log u ^ κ := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hX : 2 * (u ^ 2 / (2 * Real.log u ^ κ)) = u ^ 2 / Real.log u ^ κ := by
    rw [mul_div_assoc', mul_div_mul_left _ _ two_ne_zero]
  linarith

/-! ### Vacuity tests -/

/-- `circle_split` at `Z = 0`, `u = 1`, `m = 7`, `P = 1`, `Q = 4`: a genuine instance. -/
example : ((Rfrak 0 1 7 : ℝ) : ℂ) =
    (∫ α in majorArcs 1 4, Sexp 0 1 α ^ 3 * ee (-((7 : ℕ) * α))) +
      ∫ α in minorArcsW 1 4, Sexp 0 1 α ^ 3 * ee (-((7 : ℕ) * α)) :=
  circle_split 0 1 7 one_pos (by norm_num)

/-- The hypothesis of `Rfrak_le_of_not` holds at `Z = 0`, `u = 1`, `m = 1`: three primes
never sum to `1`. -/
theorem vacuity_not_sum : ¬ IsSum3In (↑(Pu 0 1) : Set ℕ) 1 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  have := (mem_Pu (by norm_num) (Finset.mem_coe.mp ha)).1.two_le
  omega

example : Rfrak 0 1 1 ≤ Real.log (2 * 1) ^ 3 *
    (3 * ((#(NP ⌊2 * (1 : ℝ)⌋₊) * (⌊2 * (1 : ℝ)⌋₊ + 1) : ℕ) : ℝ)) :=
  Rfrak_le_of_not 0 1 le_rfl 1 vacuity_not_sum

/-- The side condition of `repProp_of_parts` holds at `A = 1`, `B = 40`, `κ = 0`. -/
example : (0 : ℝ) < ((40 : ℕ) : ℝ) / 2 - 5 * ((1 : ℕ) : ℝ) - 5 := by norm_num

end LeanLab.SparseTernary.RepAssembly

#print axioms LeanLab.SparseTernary.RepAssembly.circle_split
#print axioms LeanLab.SparseTernary.RepAssembly.Rfrak_le_of_not
#print axioms LeanLab.SparseTernary.RepAssembly.pp_small
#print axioms LeanLab.SparseTernary.RepAssembly.repProp_of_parts
#print axioms LeanLab.SparseTernary.RepAssembly.vacuity_not_sum
