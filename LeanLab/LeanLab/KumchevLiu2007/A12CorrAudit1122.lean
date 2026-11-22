/-
UNIT P1122-0145 REPAIR, QUESTION Q1 audit of the normalization of A12Corr.
P0088, Kumchev and Liu 2007, arXiv 0801.0130, page 5 hypothesis (A1.2) and page 6
display 25, the character expansion of S1 on a major arc M(q, a).

Claim audited: the corrected hypothesis A12Corr of Prep1121KLMajorArc, through primeDefect,
puts the character on the prime weight only and puts no character on the main term
f1(m) = 1/log m. This file proves that this is exactly the normalization the character
expansion behind display 25 produces:
  S1(a/q + beta) - mu(q)/phi(q) T1(beta)
    = 1/phi(q) sum over chi of chi(a) tau(chi bar) sum over m of
      [primeDefect summand at chi] e(m beta),
when every prime of the window exceeds q. It also proves that the printed normalization,
with chi0(m)/log m as main term, differs from T1 by the terms with gcd(m, q) > 1.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc

namespace LeanLab.KumchevLiu2007.Burst1122A12Audit

open Real Complex LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- P0088 page 6 display 25, the Ramanujan sum input c_q(1) = mu(q): the sum of e(b/q)
over the reduced residues b modulo q is the Moebius function of q. -/
theorem ramanujan_one {q : ℕ} (hq : 1 ≤ q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), U1534.ee ((b : ℝ) / q) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  let c : ℕ → ℂ := fun n =>
    ∑ b ∈ (Finset.range n).filter (fun b => Nat.Coprime b n), U1534.ee ((b : ℝ) / n)
  have hfiber : ∀ n : ℕ, 0 < n → ∀ d ∈ n.divisors,
      (∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), U1534.ee ((b : ℝ) / n)) =
        c (n / d) := by
    intro n hn d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
    obtain ⟨r, rfl⟩ := Nat.dvd_of_mem_divisors hd
    rw [Nat.mul_div_cancel_left r hd0]
    dsimp [c]
    symm
    apply Finset.sum_bij (fun b _ => d * b)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨by nlinarith [hb.1], ?_⟩
      rw [Nat.gcd_mul_left, show Nat.gcd r b = 1 from hb.2.symm, mul_one]
    · intro b _ b' _ he
      exact Nat.eq_of_mul_eq_mul_left hd0 he
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      have hdb : d ∣ b := hb.2 ▸ Nat.gcd_dvd_right (d * r) b
      obtain ⟨u, rfl⟩ := hdb
      refine ⟨u, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.mul_lt_mul_left hd0).mp hb.1
      · rw [Nat.gcd_mul_left] at hb
        have hg : Nat.gcd r u = 1 := by nlinarith [hb.2]
        exact (show Nat.Coprime r u from hg).symm
    · intro b _
      have hr0 : r ≠ 0 := by intro hr; subst r; simp at hn
      have hd0' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
      unfold U1534.ee
      congr 1
      push_cast
      field_simp
      exact (mul_div_cancel_right₀ _ (by exact_mod_cast hd0.ne')).symm
  have hgroup : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, c d) =
      ∑ b ∈ Finset.range n, U1534.ee ((b : ℝ) / n) := by
    intro n hn
    rw [← Nat.sum_div_divisors n c]
    calc (∑ d ∈ n.divisors, c (n / d)) = ∑ d ∈ n.divisors,
        ∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), U1534.ee ((b : ℝ) / n) := by
          apply Finset.sum_congr rfl
          intro d hd; exact (hfiber n hn d hd).symm
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun b hb => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n b, by omega⟩) _
  have htotal : ∀ n : ℕ, 0 < n → n ∣ q →
      (∑ b ∈ Finset.range n, U1534.ee ((b : ℝ) / n)) = if n = 1 then 1 else 0 := by
    intro n hn _
    by_cases hn1 : n = 1
    · subst n; simp [U1534.ee]
    · rw [ite_eq_right hn1]
      have hp : IsPrimitiveRoot (U1534.ee ((1 : ℝ) / n)) n := by
        convert Complex.isPrimitiveRoot_exp_of_coprime 1 n (by omega) (Nat.coprime_one_left n)
          using 1
        unfold U1534.ee; push_cast; congr 1
      have hepow : ∀ b : ℕ, U1534.ee ((b : ℝ) / n) = U1534.ee ((1 : ℝ) / n) ^ b := by
        intro b
        unfold U1534.ee
        rw [← Complex.exp_nat_mul]
        congr 1; push_cast; ring
      simp_rw [hepow]
      exact hp.geom_sum_eq_zero (by omega)
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (f := c) (g := fun n => if n = 1 then (1 : ℂ) else 0) {n | n ∣ q}
    (fun m n hmn hn => hmn.trans hn)).mp
      (fun n hn hnq => (hgroup n hn).trans (htotal n hn hnq)) q (by omega) (dvd_refl q)
  rw [Nat.sum_divisorsAntidiagonal
    (fun d r => ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (if r = 1 then 1 else 0))] at hinv
  have hs : (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      (if q / d = 1 then 1 else 0)) = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    rw [Finset.sum_eq_single q]
    · rw [Nat.div_self (by omega), ite_eq_left rfl, mul_one]
    · intro d hd hdq
      have hd' := Nat.dvd_of_mem_divisors hd
      have hneq : q / d ≠ 1 := by
        intro h
        have := Nat.div_mul_cancel hd'
        rw [h, one_mul] at this
        exact hdq this
      rw [ite_eq_right hneq, mul_zero]
    · intro h; exact False.elim (h (Nat.mem_divisors_self q (by omega)))
  rw [hs] at hinv
  exact hinv.symm

/-- P0088 page 6 display 25, the Gauss sum of the principal character: tau(chi0) with the
additive character e(b/q) on ZMod q equals mu(q), the Ramanujan sum c_q(1). -/
theorem gaussSum_one_eq_moebius {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  have hsum : gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), U1534.ee ((b : ℝ) / q) := by
    unfold gaussSum
    rw [Finset.sum_filter]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr a.val_lt
    · intro a _ b _ h
      exact ZMod.val_injective q h
    · intro b hb
      refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
    · intro a _
      have hcop : IsUnit a ↔ Nat.Coprime a.val q := by
        rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      by_cases ha : IsUnit a
      · rw [MulChar.one_apply ha, one_mul, if_pos (hcop.mp ha)]
        have he := ZMod.stdAddChar_coe (N := q) (a.val : ℤ)
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at he
        rw [he]
        unfold U1534.ee
        congr 1
        push_cast
        ring
      · rw [MulChar.map_nonunit _ ha, zero_mul, if_neg (fun h => ha (hcop.mpr h))]
  rw [hsum]
  exact ramanujan_one (NeZero.pos q)

/-- P0088 page 6 display 25, the pointwise character expansion: for a unit c modulo q,
phi(q) e(c/q) is the sum over the Dirichlet characters chi modulo q of chi(c) tau(chi bar),
tau the Gauss sum with the additive character e(b/q). -/
theorem stdAddChar_char_expand {q : ℕ} [NeZero q] {c : ZMod q} (hc : IsUnit c) :
    (q.totient : ℂ) * ZMod.stdAddChar c =
      ∑ χ : DirichletCharacter ℂ q, χ c * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have key : ∀ b : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ c * χ⁻¹ b =
      if b = c then (q.totient : ℂ) else 0 := by
    intro b
    by_cases hb : IsUnit b
    · rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [mul_comm]
      congr 1
      rw [MulChar.inv_apply_eq_inv']
      have h1 : χ b * χ b⁻¹ = 1 := by
        rw [← map_mul, ZMod.mul_inv_of_unit b hb, map_one]
      exact inv_eq_of_mul_eq_one_right h1
    · have hbc : b ≠ c := fun h => hb (h ▸ hc)
      rw [if_neg hbc]
      exact Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit _ hb, mul_zero]
  simp only [gaussSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ b : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ c * (χ⁻¹ b * ZMod.stdAddChar b) =
      (if b = c then (q.totient : ℂ) else 0) * ZMod.stdAddChar b := by
    intro b
    rw [← key b, Finset.sum_mul]
    exact Finset.sum_congr rfl fun χ _ => by ring
  simp_rw [this, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ c]
  simp

/-- P0088 page 6 display 25, the shift of the argument: e(m (a/q + beta)) is the additive
character e(a m / q) on ZMod q times e(m beta). -/
theorem fourier_shift (q a m : ℕ) [NeZero q] (β : ℝ) :
    fourier (m : ℤ) (((a : ℝ) / q + β : ℝ) : AddCircle (1 : ℝ)) =
      ZMod.stdAddChar (((a * m : ℕ) : ℤ) : ZMod q) * fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0088 page 6 display 25, the main term: only the principal character carries the term
f1(m) = 1/log m, and tau(chi0) = mu(q) turns it into mu(q) T1. -/
theorem mainTerm_expand {q a : ℕ} [NeZero q] (ha : Nat.Coprime a q) (X Y β : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ a * gaussSum χ⁻¹ ZMod.stdAddChar *
        ∑ m ∈ primeWindow X Y,
          (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0) *
            fourier (m : ℤ) (β : AddCircle (1 : ℝ)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) * T1 X Y β := by
  rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
  · have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
    rw [MulChar.one_apply hu, inv_one, gaussSum_one_eq_moebius, one_mul]
    simp only [if_true, T1]
  · intro χ _ hχ
    simp [hχ]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- P0088 page 6 display 25, the prime part: summing chi(a m) tau(chi bar) over the
characters recovers phi(q) S1(a/q + beta) when every prime of the window exceeds q. -/
theorem primePart_expand {q a : ℕ} [NeZero q] (ha : Nat.Coprime a q) (X Y : ℝ)
    (hwin : ∀ m ∈ primeWindow X Y, m.Prime → q < m) (β : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ a * gaussSum χ⁻¹ ZMod.stdAddChar *
        ∑ m ∈ primeWindow X Y, (if m.Prime then χ m else 0) *
          fourier (m : ℤ) (β : AddCircle (1 : ℝ)) =
      (q.totient : ℂ) * primeSum X Y ((a : ℝ) / q + β) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, primeSum, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  by_cases hp : m.Prime
  · simp only [if_pos hp]
    have hcop : Nat.Coprime m q := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
      absurd (Nat.le_of_dvd (NeZero.pos q) h) (not_le.mpr (hwin m hm hp))
    have hu : IsUnit ((a * m : ℕ) : ZMod q) :=
      (ZMod.isUnit_iff_coprime (a * m) q).mpr (Nat.coprime_mul_iff_left.mpr ⟨ha, hcop⟩)
    have hE := stdAddChar_char_expand hu
    rw [fourier_shift q a m β, Int.cast_natCast, ← mul_assoc, hE, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ _ => ?_
    push_cast
    rw [map_mul]
    ring
  · simp [if_neg hp]

/-- P0088 page 6 display 25, the Q1 audit identity. For q at least one, a coprime to q, and
every prime of the window above q, S1(a/q + beta) minus mu(q)/phi(q) T1(beta) is
1/phi(q) times the sum over chi of chi(a) tau(chi bar) times the sum over the window of the
primeDefect summand at chi times e(m beta). So the character sits on the prime weight only
and the main term 1/log m carries none, exactly the normalization of A12Corr. -/
theorem primeSum_char_expansion {q a : ℕ} [NeZero q] (ha : Nat.Coprime a q) (X Y : ℝ)
    (hwin : ∀ m ∈ primeWindow X Y, m.Prime → q < m) (β : ℝ) :
    primeSum X Y ((a : ℝ) / q + β) -
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (q.totient : ℂ) * T1 X Y β =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ a * gaussSum χ⁻¹ ZMod.stdAddChar *
          ∑ m ∈ primeWindow X Y, ((if m.Prime then χ m else 0) -
            (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)) *
              fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [primePart_expand ha X Y hwin β, mainTerm_expand ha X Y β]
  field_simp

/-- P0088 page 5 (A1.2) and display 25: at beta = 0 the inner sum of the expansion is
literally primeDefect chi over the whole window, from X - Y to X. -/
theorem inner_sum_zero_eq_primeDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (X Y : ℝ) :
    ∑ m ∈ primeWindow X Y, ((if m.Prime then χ m else 0) -
        (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)) *
          fourier (m : ℤ) ((0 : ℝ) : AddCircle (1 : ℝ)) =
      primeDefect χ X Y (X - Y) X := by
  unfold primeDefect
  rw [Finset.filter_true_of_mem]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [fourier_coe_apply]
    simp
  · intro m hm
    simp only [primeWindow, Finset.mem_filter] at hm
    exact hm.2

/-- P0088 page 5 (A1.2) as printed, QUESTION Q1: for the principal character chi0 modulo q
the printed main term, the sum of chi0(m)/log m e(m beta) over the window, falls short of
T1(beta) by exactly the sum of 1/log m e(m beta) over the m of the window with
gcd(m, q) different from one. -/
theorem printed_mainTerm_gap {q : ℕ} [NeZero q] (X Y β : ℝ) :
    T1 X Y β - ∑ m ∈ primeWindow X Y, (1 : DirichletCharacter ℂ q) m *
        ((1 / Real.log (m : ℝ) : ℝ) : ℂ) * fourier (m : ℤ) (β : AddCircle (1 : ℝ)) =
      ∑ m ∈ (primeWindow X Y).filter (fun m => ¬ Nat.Coprime m q),
        ((1 / Real.log (m : ℝ) : ℝ) : ℂ) * fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
  rw [T1, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : Nat.Coprime m q
  · have hu : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr hm
    rw [MulChar.one_apply hu, if_neg (not_not.mpr hm)]
    ring
  · have hu : ¬ IsUnit (m : ZMod q) := fun h => hm ((ZMod.isUnit_iff_coprime m q).mp h)
    rw [MulChar.map_nonunit _ hu, if_pos hm]
    ring

#print axioms ramanujan_one
#print axioms gaussSum_one_eq_moebius
#print axioms stdAddChar_char_expand
#print axioms fourier_shift
#print axioms mainTerm_expand
#print axioms primePart_expand
#print axioms primeSum_char_expansion
#print axioms inner_sum_zero_eq_primeDefect
#print axioms printed_mainTerm_gap

end LeanLab.KumchevLiu2007.Burst1122A12Audit
