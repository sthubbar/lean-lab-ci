/-
PREP 2026-11-22, burst-20261122 unit P1122-0139, ROUTE. SPLIT of
Prep1121DKLMajorCut.S2star_M0_L1, the second factor of P0088 page 6 display 26.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, pages 3 to 6, displays 8, 14, 15,
22 and 23.

Route of the paper, page 6: on M(q, a) meeting M0 one has |beta| at most 1/(q Q0),
Q0 = Y P^(-3) by display 14; display 22 for T2 bounds the arc integral by
Y^(-1/2) log(1 + P^3); and |S(q, a)|/phi(q) is at most C q^(-1/2 + eta) by the
bound for the sum of display 8. With eta = 1/8 the sum over q at most P and a is
at most C P^(13/8), and log(1 + P^3) is at most C P^(1/8).

Proved here, with no sorry of their own:
* arc_localize: for large X a point of M0 lying on a wide arc M(q, a) of display 15
  lies on the narrow arc of display 23 with the same q and a.
* arc_eq_Icc, T2_arc_integral: the arc integral of |T2| from display 22.
* gaussS_norm_le: the bound for S(q, a), from the three gauss sum pieces below.
* arcPairs_sum_le: the sum over q at most P and a of |S(q, a)|/phi(q).
* S2star_M0_L1_of_pieces: the exact statement of S2star_M0_L1.

Pieces on the sum of display 8, which the paper uses without proof on page 6,
all three PROVED by workflow provers of session S37:
* complete_gauss_coprime, PROVED: the complete quadratic Gauss sum with coprime
  coefficient has modulus at most (2m)^(1/2).
* complete_gauss_gcd, PROVED: removing the common factor of coefficient and modulus.
* gaussS_moebius, PROVED: Moebius inversion of the condition (x, q) = 1 in display 8.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLMajorCut

namespace LeanLab.KumchevLiu2007.Prep1122S2starL1

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
  Prep1121DKLMajorCut
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-! ## The sum S(q, a) of display 8 -/

/-! Helpers for complete_gauss_coprime, proved by a workflow prover of session S37. -/

theorem sum_range_zmod_gc (m : ℕ) [NeZero m] (f : ZMod m → ℂ) :
    ∑ a ∈ Finset.range m, f (a : ZMod m) = ∑ a : ZMod m, f a := by
  apply Finset.sum_bij (s := Finset.range m) (t := (Finset.univ : Finset (ZMod m))) (fun a _ => (a : ZMod m))
  · intro a ha; exact Finset.mem_univ _
  · intro a ha b hb hab
    have h := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
  · intro a ha
    exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
  · intro a ha; rfl

theorem card_two_kernel_gc (m : ℕ) [NeZero m] :
    (Finset.univ.filter (fun h : ZMod m => 2 * h = 0)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun h : ZMod m => 2 * h = 0) ⊆ {0, ((m/2 : ℕ) : ZMod m)} := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    have h1 : m ∣ 2 * h.val := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val]; exact hh
    have hlt := ZMod.val_lt h
    obtain ⟨k, hk⟩ := h1
    have hk2 : k < 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    interval_cases k
    · have : h.val = 0 := by omega
      rw [ZMod.val_eq_zero] at this
      simp [this]
    · have : h.val = m / 2 := by omega
      have h2 : h = ((m/2 : ℕ) : ZMod m) := by
        rw [← this, ZMod.natCast_zmod_val]
      simp [h2]
  calc _ ≤ ({0, ((m/2 : ℕ) : ZMod m)} : Finset (ZMod m)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- PROVED. P0088 page 3 display 8 as used on page 6 displays 24 and 26, the complete
quadratic Gauss sum. For m at least one and c coprime to m the sum over y modulo m
of e(c y^2 / m) has modulus at most (2m)^(1/2), by Weyl differencing: the square
modulus is a sum over h of e(c h^2/m) times a complete linear sum that vanishes
unless m divides 2h. -/
theorem complete_gauss_coprime (m c : ℕ) (hm : 1 ≤ m) (hc : Nat.Coprime c m) :
    ‖∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ))‖ ≤
      Real.sqrt (2 * m) := by
  have : NeZero m := ⟨by omega⟩
  set ψ := (ZMod.stdAddChar (N := m)) with hψ
  have std_int (a : ℤ) : U1534.ee ((a : ℝ) / m) = ψ (a : ZMod m) := by
    rw [hψ, ZMod.stdAddChar_coe]
    unfold U1534.ee
    congr 1
    push_cast
    ring
  have std_nat (a : ℕ) : U1534.ee ((a : ℝ) / m) = ψ (a : ZMod m) := by
    simpa using std_int (a : ℤ)
  set c' : ZMod m := (c : ZMod m) with hc'
  have hG : ∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ)) =
      ∑ x : ZMod m, ψ (c' * x ^ 2) := by
    simp_rw [std_nat]
    push_cast
    exact sum_range_zmod_gc m (fun a => ψ (c' * a ^ 2))
  rw [hG]
  set G := ∑ x : ZMod m, ψ (c' * x ^ 2) with hGdef
  have hconj : (starRingEnd ℂ) G = ∑ y : ZMod m, ψ (-(c' * y ^ 2)) := by
    rw [hGdef, map_sum]
    simp_rw [AddChar.map_neg_eq_conj]
  have hprod : G * (starRingEnd ℂ) G =
      ∑ h : ZMod m, ψ (c' * h ^ 2) * ∑ y : ZMod m, ψ (y * (2 * c' * h)) := by
    rw [hconj, hGdef, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Equiv.sum_comp (Equiv.addRight y)]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [Equiv.coe_addRight]
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hprim := ZMod.isPrimitive_stdAddChar m
  have hprod2 : G * (starRingEnd ℂ) G =
      ∑ h : ZMod m, ψ (c' * h ^ 2) * (if 2 * h = 0 then (m : ℂ) else 0) := by
    rw [hprod]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [AddChar.sum_mulShift _ hprim, ZMod.card]
    have hu : IsUnit c' := (ZMod.isUnit_iff_coprime c m).mpr hc
    have : (2 * c' * h = 0) ↔ (2 * h = 0) := by
      rw [show 2 * c' * h = c' * (2 * h) by ring]
      exact hu.mul_right_eq_zero
    simp only [this]
    push_cast
    rfl
  have hnorm : ‖G‖ ^ 2 ≤ 2 * m := by
    have e1 : ‖G‖ ^ 2 = ‖G * (starRingEnd ℂ) G‖ := by
      rw [norm_mul, RCLike.norm_conj, sq]
    rw [e1, hprod2]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ h : ZMod m, ‖ψ (c' * h ^ 2) * (if 2 * h = 0 then (m : ℂ) else 0)‖
        = ∑ h : ZMod m, (if 2 * h = 0 then (m : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          rw [norm_mul, hψ, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
          split_ifs <;> simp
      _ = ((Finset.univ.filter (fun h : ZMod m => 2 * h = 0)).card : ℝ) * m := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * m := by
          have := card_two_kernel_gc m
          have h2 : ((Finset.univ.filter (fun h : ZMod m => 2 * h = 0)).card : ℝ) ≤ 2 := by
            exact_mod_cast this
          nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  exact Real.le_sqrt_of_sq_le hnorm

/-! Helpers for complete_gauss_gcd, proved by a workflow prover of session S37. -/

lemma ee_add_nat_gcd (x : ℝ) (N : ℕ) : U1534.ee (x + N) = U1534.ee x := by
  unfold U1534.ee
  have : (2 * (Real.pi : ℂ) * Complex.I * ((x + N : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (x : ℂ) + (N : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma ee_period_gcd (c' n k y : ℕ) (hn : 0 < n) :
    U1534.ee (((c' * (n * k + y) ^ 2 : ℕ) : ℝ) / (n : ℝ)) =
      U1534.ee (((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : ((c' * (n * k + y) ^ 2 : ℕ) : ℝ) / (n : ℝ) =
      ((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ) + ((c' * (n * k ^ 2 + 2 * k * y) : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [this, ee_add_nat_gcd]

lemma sum_blocks_gcd (c' n : ℕ) (hn : 0 < n) (g : ℕ) :
    (∑ y ∈ Finset.range (n * g), U1534.ee (((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ))) =
      (g : ℂ) * ∑ y ∈ Finset.range n, U1534.ee (((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ)) := by
  induction g with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [ee_period_gcd c' n k _ hn]
    push_cast; ring

/-- PROVED. P0088 page 3 display 8 as used on page 6, the common factor step for the
complete quadratic sum. With g = (c, m), each term e(c y^2 / m) equals
e((c/g) y^2 / (m/g)), which has period m/g in y, so the sum over y modulo m is g
times the sum over y modulo m/g. -/
theorem complete_gauss_gcd (m c : ℕ) (hm : 1 ≤ m) :
    (∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ))) =
      (Nat.gcd c m : ℂ) * ∑ y ∈ Finset.range (m / Nat.gcd c m),
        U1534.ee ((((c / Nat.gcd c m) * y ^ 2 : ℕ) : ℝ) / ((m / Nat.gcd c m : ℕ) : ℝ)) := by
  set g := Nat.gcd c m with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hm' : m = (m / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right c m)).symm
  have hc' : c = (c / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left c m)).symm
  have hnpos : 0 < m / g := Nat.div_pos (Nat.gcd_le_right _ hm) hgpos
  rw [← sum_blocks_gcd (c / g) (m / g) hnpos g, ← hm']
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  conv_lhs => rw [hc', hm']
  push_cast
  field_simp

/-! Helpers for gaussS_moebius, proved by a workflow prover of session S37. -/

theorem moebius_sum_divisors_complex (n : ℕ) (_hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

theorem filter_dvd_range_eq (a q d : ℕ) (hd : d ∣ q) (hd0 : 0 < d) :
    ∑ x ∈ (Finset.range q).filter (fun x => d ∣ x), (fun x => U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ))) x
      = ∑ y ∈ Finset.range (q / d), U1534.ee ((((a * d) * y ^ 2 : ℕ) : ℝ) / ((q / d : ℕ) : ℝ)) := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left k hd0]
  symm
  refine Finset.sum_nbij' (fun y => d * y) (fun x => x / d) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
    exact ⟨Nat.mul_lt_mul_of_pos_left hy hd0, dvd_mul_right _ _⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact Nat.div_lt_of_lt_mul hx.1
  · intro y _
    simp [Nat.mul_div_cancel_left y hd0]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact Nat.mul_div_cancel' hx.2
  · intro y hy
    simp only [Finset.mem_range] at hy
    have hk : 0 < k := by omega
    congr 1
    push_cast
    field_simp

/-- PROVED. P0088 page 3 display 8, the reduced sum S(q, a) by Moebius inversion of
the condition (x, q) = 1: the residues x = d y with d dividing q give
S(q, a) = sum over d dividing q of mu(d) times the complete sum over y modulo q/d
of e(a d y^2 / (q/d)). -/
theorem gaussS_moebius (q a : ℕ) (hq : 1 ≤ q) :
    U1534.gaussS q a = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ∑ y ∈ Finset.range (q / d), U1534.ee ((((a * d) * y ^ 2 : ℕ) : ℝ) / ((q / d : ℕ) : ℝ)) := by
  unfold U1534.gaussS
  rw [Finset.sum_filter]
  have step : ∀ x ∈ Finset.range q,
      (if Nat.Coprime x q then U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ)) else 0)
        = ∑ d ∈ q.divisors, (if d ∣ x then ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ)) else 0) := by
    intro x _
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    have hfil : q.divisors.filter (fun d => d ∣ x) = (Nat.gcd x q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, Nat.gcd_pos_of_pos_right _ (by omega) |>.ne'⟩
      · rintro ⟨⟨h3, h1⟩, _⟩; exact ⟨⟨h1, by omega⟩, h3⟩
    rw [hfil, moebius_sum_divisors_complex _ (Nat.gcd_pos_of_pos_right _ (by omega))]
    unfold Nat.Coprime
    split_ifs <;> simp
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  have hd' := Nat.mem_divisors.mp hd
  exact filter_dvd_range_eq a q d hd'.1 (Nat.pos_of_mem_divisors hd)

/-- PROVED. P0088 page 3 display 8, the complete quadratic sum with any coefficient:
modulus at most (2 m (c, m))^(1/2), from complete_gauss_gcd and complete_gauss_coprime. -/
theorem complete_gauss_le (m c : ℕ) (hm : 1 ≤ m) :
    ‖∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ))‖ ≤
      Real.sqrt (2 * m * Nat.gcd c m) := by
  set g := Nat.gcd c m with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right c (by omega)
  have hgm : g ∣ m := Nat.gcd_dvd_right c m
  have hgc : g ∣ c := Nat.gcd_dvd_left c m
  have hm' : 1 ≤ m / g := (Nat.one_le_div_iff hg0).mpr (Nat.le_of_dvd (by omega) hgm)
  have hcop : Nat.Coprime (c / g) (m / g) := Nat.coprime_div_gcd_div_gcd hg0
  rw [complete_gauss_gcd m c hm, norm_mul, Complex.norm_natCast]
  have h1 := complete_gauss_coprime (m / g) (c / g) hm' hcop
  have hmg : ((m / g : ℕ) : ℝ) = (m : ℝ) / g := by
    rw [Nat.cast_div hgm (by exact_mod_cast hg0.ne')]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  calc (g : ℝ) * ‖_‖ ≤ g * Real.sqrt (2 * ((m / g : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hgR.le
    _ = Real.sqrt (2 * m * g) := by
        rw [hmg, show (2 : ℝ) * m * g = (g : ℝ) ^ 2 * (2 * ((m : ℝ) / g)) by field_simp,
          Real.sqrt_mul (x := (g : ℝ) ^ 2) (by positivity), Real.sqrt_sq hgR.le]

/-- PROVED. The divisor bound with exponent 1/8. Copy of the proved
BHP1997.Decomp312c.card_divisors_le_rpow, which is private there. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

/-- PROVED. P0088 page 3 display 8, the bound used on page 6: for a coprime to q,
|S(q, a)| is at most C q^(1/2 + eta) with eta = 1/8. From gaussS_moebius,
complete_gauss_le, (a d, q/d) = (d, q/d) at most d, and the divisor bound. -/
theorem gaussS_norm_le : ∃ C : ℝ, 0 < C ∧ ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
    ‖U1534.gaussS q a‖ ≤ C * (q : ℝ) ^ (5 / 8 : ℝ) := by
  obtain ⟨Cd, hCd, hd⟩ := card_divisors_le_rpow (ε := 1 / 8) (by norm_num)
  refine ⟨Cd * Real.sqrt 2, by positivity, fun q a hq ha => ?_⟩
  rw [gaussS_moebius q a hq]
  have hterm : ∀ d ∈ q.divisors, ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ∑ y ∈ Finset.range (q / d), U1534.ee ((((a * d) * y ^ 2 : ℕ) : ℝ) / ((q / d : ℕ) : ℝ))‖ ≤
        Real.sqrt (2 * q) := by
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hqd : 1 ≤ q / d := (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdq)
    have hmu : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hcop : Nat.Coprime a (q / d) := Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdq) ha
    have hgcd : Nat.gcd (a * d) (q / d) ≤ d := by
      rw [Nat.Coprime.gcd_mul_left_cancel d hcop]
      exact Nat.le_of_dvd hd0 (Nat.gcd_dvd_left _ _)
    have hprod : ((q / d : ℕ) : ℝ) * (Nat.gcd (a * d) (q / d) : ℝ) ≤ q := by
      have h : (q / d) * Nat.gcd (a * d) (q / d) ≤ q :=
        (Nat.mul_le_mul_left _ hgcd).trans (Nat.div_mul_cancel hdq).le
      exact_mod_cast h
    rw [norm_mul]
    calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖_‖
        ≤ 1 * Real.sqrt (2 * ((q / d : ℕ) : ℝ) * (Nat.gcd (a * d) (q / d) : ℝ)) :=
          mul_le_mul hmu (complete_gauss_le (q / d) (a * d) hqd) (norm_nonneg _) zero_le_one
      _ ≤ Real.sqrt (2 * q) := by
          rw [one_mul, mul_assoc]
          exact Real.sqrt_le_sqrt (by linarith)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  calc ‖∑ d ∈ q.divisors, _‖ ≤ ∑ d ∈ q.divisors, Real.sqrt (2 * q) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (q.divisors.card : ℝ) * Real.sqrt (2 * q) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cd * (q : ℝ) ^ (1 / 8 : ℝ)) * Real.sqrt (2 * q) :=
        mul_le_mul_of_nonneg_right (hd q) (Real.sqrt_nonneg _)
    _ = Cd * Real.sqrt 2 * (q : ℝ) ^ (5 / 8 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (q : ℝ)]
        have : (q : ℝ) ^ (1 / 8 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) = (q : ℝ) ^ (5 / 8 : ℝ) := by
          rw [← Real.rpow_add hq0]; norm_num
        rw [← this]; ring

/-! ## The arcs of displays 15 and 23 -/

/-- PROVED. P0088 page 4 display 15: the closed arc of width R^(-1) in q alpha is the
interval of half length R^(-1)/q about a/q. -/
theorem arc_eq_Icc (R : ℝ) (v : ℕ × ℕ) (hq : 1 ≤ v.1) :
    arc R v = Set.Icc ((v.2 : ℝ) / v.1 - R⁻¹ / v.1) ((v.2 : ℝ) / v.1 + R⁻¹ / v.1) := by
  have hq0 : (0 : ℝ) < v.1 := by exact_mod_cast hq
  ext α
  simp only [arc, Set.mem_setOf_eq, Set.mem_Icc]
  have h : (v.1 : ℝ) * α - v.2 = v.1 * (α - v.2 / v.1) := by field_simp
  rw [h, abs_mul, abs_of_pos hq0, ← le_div_iff₀' hq0, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- PROVED. P0088 page 4 display 15 and page 6 display 23: an arc about a/q and an arc
about a'/q', both fractions reduced, meet only when q = q' and a = a', once
q' r1 + q r2 < 1, since otherwise |a q' - a' q| is at least one. -/
theorem arc_localize {q q' a : ℕ} {a' : ℤ} {α r1 r2 : ℝ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (ha : Nat.Coprime a q) (ha' : IsCoprime a' (q' : ℤ))
    (h1 : |(q : ℝ) * α - a| ≤ r1) (h2 : |(q' : ℝ) * α - a'| ≤ r2)
    (hsmall : (q' : ℝ) * r1 + q * r2 < 1) : q = q' ∧ (a : ℤ) = a' := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq0' : (0 : ℝ) ≤ q' := by positivity
  have hk : |(((a : ℤ) * q' - a' * q : ℤ) : ℝ)| < 1 := by
    have e : (((a : ℤ) * q' - a' * q : ℤ) : ℝ) =
        q * ((q' : ℝ) * α - a') - q' * ((q : ℝ) * α - a) := by push_cast; ring
    rw [e]
    calc |(q : ℝ) * ((q' : ℝ) * α - a') - q' * ((q : ℝ) * α - a)|
        ≤ |(q : ℝ) * ((q' : ℝ) * α - a')| + |(q' : ℝ) * ((q : ℝ) * α - a)| := abs_sub _ _
      _ = q * |(q' : ℝ) * α - a'| + q' * |(q : ℝ) * α - a| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hq0']
      _ ≤ q * r2 + q' * r1 :=
          add_le_add (mul_le_mul_of_nonneg_left h2 hq0) (mul_le_mul_of_nonneg_left h1 hq0')
      _ < 1 := by linarith
  have hk' : |((a : ℤ) * q' - a' * q)| < 1 := by
    have : ((|((a : ℤ) * q' - a' * q)| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hk
    exact_mod_cast this
  have hk0 : (a : ℤ) * q' = a' * q := by
    have := Int.abs_lt_one_iff.mp hk'
    linarith
  have hca : IsCoprime (a : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ha
  have hd1 : (q : ℤ) ∣ q' := by
    apply hca.symm.dvd_of_dvd_mul_right
    exact ⟨a', by rw [mul_comm, hk0, mul_comm]⟩
  have hd2 : (q' : ℤ) ∣ q := by
    apply ha'.symm.dvd_of_dvd_mul_right
    exact ⟨a, by rw [mul_comm, ← hk0, mul_comm]⟩
  have hqq : q = q' := Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp hd1)
    (Int.natCast_dvd_natCast.mp hd2)
  refine ⟨hqq, ?_⟩
  subst hqq
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  exact mul_right_cancel₀ hqz hk0

/-- PROVED. P0088 page 6 display 26, the pointwise step: on M0, for large X, every wide
arc M(q, a) of display 15 through alpha is the narrow arc of display 23 with the same
q and a, so |S2*(alpha)| is at most the sum over the narrow arcs through alpha of
|S(q, a)|/phi(q) |T2(alpha - a/q)|. -/
theorem S2star_norm_le_on_M0 {Y H P α : ℝ} (hP : 1 ≤ P)
    (hsmall : P * (H / P)⁻¹ + P * (Y * P ^ (-2 : ℤ) / P)⁻¹ < 1)
    (hα : α ∈ majorArcs (Y * P ^ (-2 : ℤ)) P) :
    ‖S2star Y H P α‖ ≤ ∑ v ∈ arcPairs P, (arc (Y * P ^ (-2 : ℤ) / P) v).indicator
      (fun α => ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ) *
        ‖T2 Y P (α - v.2 / v.1)‖) α := by
  obtain ⟨q', hq'1, hq'P, a', ha', hclose⟩ := hα
  unfold S2star
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v hv => ?_)
  obtain ⟨hvprod, _, hvcop⟩ := Finset.mem_filter.mp hv
  rw [Finset.mem_product, Finset.mem_Icc] at hvprod
  have hq1 : 1 ≤ v.1 := hvprod.1.1
  have hqP : (v.1 : ℝ) ≤ P := (Nat.cast_le.mpr hvprod.1.2).trans (Nat.floor_le (by linarith))
  by_cases hin : α ∈ arc (H / P) v
  · rw [Set.indicator_of_mem hin]
    have hin' : |(v.1 : ℝ) * α - v.2| ≤ (H / P)⁻¹ := hin
    have hr1 : 0 ≤ (H / P)⁻¹ := (abs_nonneg _).trans hin'
    have hr2 : 0 ≤ (Y * P ^ (-2 : ℤ) / P)⁻¹ := (abs_nonneg _).trans hclose
    have hq'P' : (q' : ℝ) ≤ P := hq'P
    obtain ⟨hqq, haa⟩ := arc_localize hq1 hq'1 hvcop ha' hin' hclose (by
      have := mul_le_mul_of_nonneg_right hq'P' hr1
      have := mul_le_mul_of_nonneg_right hqP hr2
      linarith)
    have hin0 : α ∈ arc (Y * P ^ (-2 : ℤ) / P) v := by
      show |(v.1 : ℝ) * α - v.2| ≤ _
      have e1 : (v.1 : ℝ) = q' := by exact_mod_cast hqq
      have e2 : ((v.2 : ℕ) : ℝ) = (a' : ℝ) := by
        rw [← haa]; norm_cast
      rw [e1, e2]; exact hclose
    rw [Set.indicator_of_mem hin0, norm_mul, norm_div, Complex.norm_natCast]
  · rw [Set.indicator_of_notMem hin, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _

/-! ## The arc integral of T2 from display 22 -/

/-- PROVED. P0088 page 6 display 26: on an arc of width R^(-1) in q alpha, display 22
for T2, |T2(beta)| at most C Y^(1/2)/(1 + Y |beta|), integrates to at most
2 C Y^(-1/2) log(1 + Y R^(-1)). -/
theorem T2_arc_integral {Y P C R : ℝ} (v : ℕ × ℕ) (hq : 1 ≤ v.1) (hY : 0 < Y) (hR : 0 < R)
    (hC : 0 ≤ C)
    (hT : ∀ β : ℝ, |β| ≤ R⁻¹ → ‖T2 Y P β‖ ≤ C * Real.sqrt Y / (1 + Y * |β|)) :
    ∫ α in arc R v, ‖T2 Y P (α - v.2 / v.1)‖ ≤
      2 * C * Real.log (1 + Y * R⁻¹) / Real.sqrt Y := by
  have hq0 : (0 : ℝ) < v.1 := by exact_mod_cast hq
  have hw : 0 ≤ R⁻¹ / v.1 := by positivity
  have hwR : R⁻¹ / v.1 ≤ R⁻¹ := div_le_self (inv_nonneg.mpr hR.le) (by exact_mod_cast hq)
  set w := R⁻¹ / v.1 with hwdef
  rw [arc_eq_Icc R v hq, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun β => ‖T2 Y P β‖)]
  have e1 : (v.2 : ℝ) / v.1 - w - v.2 / v.1 = -w := by ring
  have e2 : (v.2 : ℝ) / v.1 + w - v.2 / v.1 = w := by ring
  rw [e1, e2]
  set g : ℝ → ℝ := fun β => C * Real.sqrt Y / (1 + Y * |β|) with hg
  have hgc : Continuous g := by
    refine Continuous.div continuous_const (by fun_prop) (fun β => ?_)
    have : 0 ≤ Y * |β| := by positivity
    linarith
  have hTc : Continuous fun β => ‖T2 Y P β‖ := (trig_continuous _ _ _).norm
  have h1 : (∫ β in -w..w, ‖T2 Y P β‖) ≤ ∫ β in -w..w, g β :=
    intervalIntegral.integral_mono_on (by linarith) (hTc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)
      (fun β hβ => hT β (by rw [abs_le]; constructor <;> linarith [hβ.1, hβ.2]))
  have hsplit : (∫ β in -w..w, g β) = 2 * ∫ β in (0 : ℝ)..w, g β := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := w) g
    rw [neg_zero] at h
    have hge : (fun x => g (-x)) = g := by
      funext x; simp only [hg, abs_neg]
    rw [hge] at h
    rw [← h]; ring
  have heval : (∫ β in (0 : ℝ)..w, g β) = C * Real.sqrt Y * (Real.log (1 + Y * w) / Y) := by
    have hcongr : (∫ β in (0 : ℝ)..w, g β) =
        ∫ β in (0 : ℝ)..w, C * Real.sqrt Y * (1 + Y * β)⁻¹ := by
      refine intervalIntegral.integral_congr (fun β hβ => ?_)
      rw [Set.uIcc_of_le hw] at hβ
      simp only [hg, abs_of_nonneg hβ.1, div_eq_mul_inv]
    rw [hcongr, intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_comp_add_mul (fun x : ℝ => x⁻¹) hY.ne' 1 (a := 0) (b := w)
    rw [this, mul_zero, add_zero, integral_inv_of_pos one_pos (by positivity), div_one,
      smul_eq_mul]
    ring
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hlog : Real.log (1 + Y * w) ≤ Real.log (1 + Y * R⁻¹) :=
    Real.log_le_log (by positivity) (by nlinarith)
  calc (∫ β in -w..w, ‖T2 Y P β‖) ≤ ∫ β in -w..w, g β := h1
    _ = 2 * (C * Real.sqrt Y * (Real.log (1 + Y * w) / Y)) := by rw [hsplit, heval]
    _ = 2 * C * Real.log (1 + Y * w) * (Real.sqrt Y / Y) := by ring
    _ = 2 * C * Real.log (1 + Y * w) / Real.sqrt Y := by
        have : Real.sqrt Y / Y = 1 / Real.sqrt Y := by
          rw [div_eq_div_iff hY.ne' hsY.ne', one_mul, Real.mul_self_sqrt hY.le]
        rw [this]; ring
    _ ≤ 2 * C * Real.log (1 + Y * R⁻¹) / Real.sqrt Y := by
        apply div_le_div_of_nonneg_right _ hsY.le
        exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-! ## The sum over the arcs -/

/-- PROVED. P0088 page 6 display 26, the sum over q at most P and a of |S(q, a)|/phi(q):
with |S(q, a)| at most C q^(5/8), at most phi(q) + 1 values of a for each q, and
q at most P, the sum is at most 2 C P^(13/8). -/
theorem arcPairs_sum_le {C P : ℝ} (hC : 0 < C) (hP : 1 ≤ P)
    (hS : ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
      ‖U1534.gaussS q a‖ ≤ C * (q : ℝ) ^ (5 / 8 : ℝ)) :
    ∑ v ∈ arcPairs P, ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ) ≤
      2 * C * P ^ (13 / 8 : ℝ) := by
  have hP0 : 0 ≤ P := by linarith
  have hinner : ∀ q ∈ Finset.Icc 1 ⌊P⌋₊,
      (∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
        ‖U1534.gaussS q a‖ / (Nat.totient q : ℝ)) ≤ 2 * C * P ^ (5 / 8 : ℝ) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hφpos : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφpos
    have hcard : ((Finset.range (⌊P⌋₊ + 1)).filter
        (fun a => a ≤ q ∧ Nat.Coprime a q)).card ≤ 2 * Nat.totient q := by
      have hsub : (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q) ⊆
          insert q ((Finset.range q).filter (fun a => q.Coprime a)) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        rcases eq_or_lt_of_le ha.2.1 with h | h
        · simp [h]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, ha.2.2.symm⟩)
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ((Finset.range q).filter (fun a => q.Coprime a)).card + 1 :=
            Finset.card_insert_le _ _
        _ = Nat.totient q + 1 := by rw [Nat.totient_eq_card_coprime]
        _ ≤ 2 * Nat.totient q := by omega
    have hqP : (q : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hP0)
    have hterm : ∀ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
        ‖U1534.gaussS q a‖ / (Nat.totient q : ℝ) ≤ C * P ^ (5 / 8 : ℝ) / Nat.totient q := by
      intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      apply div_le_div_of_nonneg_right _ hφ.le
      exact (hS q a hq.1 ha'.2).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hqP (by norm_num)) hC.le)
    calc _ ≤ ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          C * P ^ (5 / 8 : ℝ) / Nat.totient q := Finset.sum_le_sum hterm
      _ = (((Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q)).card : ℝ) *
          (C * P ^ (5 / 8 : ℝ) / Nat.totient q) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * Nat.totient q : ℝ) * (C * P ^ (5 / 8 : ℝ) / Nat.totient q) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 2 * C * P ^ (5 / 8 : ℝ) := by field_simp
  have hsplit : (∑ v ∈ arcPairs P, ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ)) =
      ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
        ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          ‖U1534.gaussS q a‖ / (Nat.totient q : ℝ) := by
    unfold arcPairs
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_filter]
  rw [hsplit]
  calc _ ≤ ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, 2 * C * P ^ (5 / 8 : ℝ) := Finset.sum_le_sum hinner
    _ = (⌊P⌋₊ : ℝ) * (2 * C * P ^ (5 / 8 : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ P * (2 * C * P ^ (5 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hP0) (by positivity)
    _ = 2 * C * P ^ (13 / 8 : ℝ) := by
        rw [show (13 / 8 : ℝ) = 1 + 5 / 8 by norm_num, Real.rpow_add (by linarith),
          Real.rpow_one]
        ring

/-- PROVED. log(1 + P^3) is at most 25 P^(1/8) for P at least one; the log factor of
display 26 is absorbed by eta = 1/8. -/
theorem log_one_add_cube_le {P : ℝ} (hP : 1 ≤ P) :
    Real.log (1 + P ^ 3) ≤ 25 * P ^ (1 / 8 : ℝ) := by
  have hP0 : 0 < P := by linarith
  have hP3 : 1 ≤ P ^ 3 := one_le_pow₀ hP
  have h1 : Real.log (1 + P ^ 3) ≤ Real.log (2 * P ^ 3) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
  have h2 : Real.log P ≤ P ^ (1 / 8 : ℝ) / (1 / 8) := Real.log_le_rpow_div hP0.le (by norm_num)
  have h3 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have h4 : 1 ≤ P ^ (1 / 8 : ℝ) := Real.one_le_rpow hP (by norm_num)
  push_cast at h1
  have h2' : Real.log P ≤ 8 * P ^ (1 / 8 : ℝ) := by
    have : P ^ (1 / 8 : ℝ) / (1 / 8) = 8 * P ^ (1 / 8 : ℝ) := by ring
    linarith
  linarith

/-- PROVED. For large X, 4 (log X)^(6B) is at most X^(1/4), since every power of
log X is o(X^(1/4)). -/
theorem eventually_small (B : ℝ) :
    ∃ X0 : ℝ, ∀ X, X0 ≤ X → 3 ≤ X ∧ 4 * (Real.log X ^ B) ^ 6 ≤ X ^ (1 / 4 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (6 * B) (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp h
  refine ⟨max X1 3, fun X hX => ⟨(le_max_right _ _).trans hX, ?_⟩⟩
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hb := hX1 X ((le_max_left _ _).trans hX)
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hb
  have hpow : (Real.log X ^ B) ^ 6 = Real.log X ^ (6 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; ring_nf
  rw [hpow]; linarith

/-! ## Assembly -/

/-- The exact statement of Prep1121DKLMajorCut.S2star_M0_L1, P0088 page 6 display 26
second factor, from S2star_norm_le_on_M0, T2_arc_integral, arcPairs_sum_le,
gaussS_norm_le and log_one_add_cube_le. No sorry anywhere: PROVED,
CONDITIONAL ON T2BoundProp, display 22 for T2. -/
theorem S2star_M0_L1_of_pieces (h2 : T2BoundProp) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B),
          ‖S2star (windowY X ε) H (Real.log X ^ B) α‖) ≤
            C * (Real.log X ^ B) ^ (7 / 4 : ℝ) / Real.sqrt (windowY X ε) := by
  intro B hB ε hε hε'
  obtain ⟨CT, XT, hCT, hT⟩ := h2 B hB ε hε hε'
  obtain ⟨CG, hCG, hG⟩ := gaussS_norm_le
  obtain ⟨XE, hE⟩ := eventually_small B
  refine ⟨2 * CG * (2 * CT * 25), max XT XE, by positivity, ?_⟩
  intro X H hX hlo _hhi
  obtain ⟨hX3, hsm⟩ := hE X ((le_max_right _ _).trans hX)
  have hT' := hT X ((le_max_left _ _).trans hX)
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX3
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hY1 := Prep1121DKLMajorCut.windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  have hsY : X ^ (1 / 4 : ℝ) ≤ Real.sqrt (windowY X ε) := by
    rw [windowY, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hX14 : X ^ (1 / 4 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set Y := windowY X ε with hYdef
  set P := Real.log X ^ B with hPdef
  have hP0 : 0 < P := by linarith
  have hY0 : 0 < Y := by linarith
  have hsY0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
  have hsqY : Real.sqrt Y ≤ Y := by nlinarith
  have hP3 : P ^ 3 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP4 : P ^ 4 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  -- the narrow arc width
  set R0 := Y * P ^ (-2 : ℤ) / P with hR0
  have hR0pos : 0 < R0 := by positivity
  have hR0inv : R0⁻¹ = P ^ 3 / Y := by
    rw [hR0, zpow_neg, zpow_ofNat]; field_simp
  -- the lower bound for H
  have hPm4 : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg, zpow_ofNat]
  have hH : 4 * P ^ 2 ≤ H := by
    rw [hPm4] at hlo
    have h4 : X ^ (1 / 4 : ℝ) * (P ^ 4)⁻¹ ≤ H :=
      (mul_le_mul_of_nonneg_right hX14 (by positivity)).trans hlo
    have h5 : 4 * P ^ 2 = 4 * P ^ 6 * (P ^ 4)⁻¹ := by field_simp
    rw [h5]
    exact (mul_le_mul_of_nonneg_right hsm (by positivity)).trans h4
  have hH0 : 0 < H := by nlinarith
  have hsmall : P * (H / P)⁻¹ + P * R0⁻¹ < 1 := by
    have e1 : P * (H / P)⁻¹ = P ^ 2 / H := by field_simp
    rw [e1, hR0inv]
    have a1 : P ^ 2 / H ≤ 1 / 4 := by
      rw [div_le_iff₀ hH0]; linarith
    have a2 : P * (P ^ 3 / Y) ≤ 1 / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ hY0]; nlinarith
    linarith
  -- display 22 for T2 on the narrow arcs
  have hTarc : ∀ β : ℝ, |β| ≤ R0⁻¹ → ‖T2 Y P β‖ ≤ CT * Real.sqrt Y / (1 + Y * |β|) := by
    intro β hβ
    apply hT' β
    rw [hR0inv] at hβ
    refine hβ.trans ?_
    have h4 : 4 * P ^ 3 ≤ Real.sqrt Y := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right h4 hsY0.le
    rw [div_le_div_iff₀ hY0 (by positivity)]
    nlinarith
  have hlogP : Real.log (1 + Y * R0⁻¹) ≤ 25 * P ^ (1 / 8 : ℝ) := by
    rw [hR0inv, mul_div_cancel₀ _ hY0.ne']
    exact log_one_add_cube_le hP1
  -- the majorant
  set K : ℕ × ℕ → ℝ := fun v => ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ) with hK
  set G : ℝ → ℝ := fun α => ∑ v ∈ arcPairs P, (arc R0 v).indicator
    (fun α => K v * ‖T2 Y P (α - v.2 / v.1)‖) α with hGdef
  have hv1 : ∀ v ∈ arcPairs P, 1 ≤ v.1 := by
    intro v hv
    obtain ⟨hvprod, _⟩ := Finset.mem_filter.mp hv
    rw [Finset.mem_product, Finset.mem_Icc] at hvprod
    exact hvprod.1.1
  have hint : ∀ v ∈ arcPairs P,
      Integrable ((arc R0 v).indicator (fun α => K v * ‖T2 Y P (α - v.2 / v.1)‖)) := by
    intro v hv
    rw [integrable_indicator_iff (Prep1121DKLMajorCut.measurableSet_arc R0 v), arc_eq_Icc R0 v (hv1 v hv)]
    exact (continuous_const.mul
      ((trig_continuous _ _ _).comp (continuous_sub_right _)).norm).integrableOn_Icc
  have hGint : Integrable G := integrable_finsetSum _ hint
  have hG0 : ∀ α, 0 ≤ G α := fun α =>
    Finset.sum_nonneg fun v _ => Set.indicator_nonneg (fun _ _ => by positivity) _
  set S := Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P with hS
  have hSm : MeasurableSet S := measurableSet_Ioc.inter (measurableSet_majorArcs _ P)
  have step1 : (∫ α in S, ‖S2star Y H P α‖) ≤ ∫ α in S, G α :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun α => norm_nonneg _)
      hGint.integrableOn
      (ae_restrict_of_forall_mem hSm fun α hα => S2star_norm_le_on_M0 hP1 hsmall hα.2)
  have step2 : (∫ α in S, G α) ≤ ∫ α, G α :=
    setIntegral_le_integral hGint (Filter.Eventually.of_forall hG0)
  have step3 : (∫ α, G α) = ∑ v ∈ arcPairs P, K v * ∫ α in arc R0 v,
      ‖T2 Y P (α - v.2 / v.1)‖ := by
    rw [hGdef, integral_finset_sum _ hint]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_indicator (Prep1121DKLMajorCut.measurableSet_arc R0 v), integral_const_mul]
  have hL0 : 0 ≤ Real.log (1 + Y * R0⁻¹) := Real.log_nonneg (by
    have : 0 ≤ Y * R0⁻¹ := by positivity
    linarith)
  have step4 : (∑ v ∈ arcPairs P, K v * ∫ α in arc R0 v, ‖T2 Y P (α - v.2 / v.1)‖) ≤
      (∑ v ∈ arcPairs P, K v) * (2 * CT * Real.log (1 + Y * R0⁻¹) / Real.sqrt Y) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun v hv => ?_
    exact mul_le_mul_of_nonneg_left
      (T2_arc_integral v (hv1 v hv) hY0 hR0pos hCT.le hTarc) (by positivity)
  have step5 : (∑ v ∈ arcPairs P, K v) ≤ 2 * CG * P ^ (13 / 8 : ℝ) :=
    arcPairs_sum_le hCG hP1 hG
  have hfin : (∑ v ∈ arcPairs P, K v) * (2 * CT * Real.log (1 + Y * R0⁻¹) / Real.sqrt Y) ≤
      2 * CG * (2 * CT * 25) * P ^ (7 / 4 : ℝ) / Real.sqrt Y := by
    have hA : (2 * CT * Real.log (1 + Y * R0⁻¹) / Real.sqrt Y) ≤
        2 * CT * (25 * P ^ (1 / 8 : ℝ)) / Real.sqrt Y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogP (by positivity)) hsY0.le
    have hpp : P ^ (13 / 8 : ℝ) * P ^ (1 / 8 : ℝ) = P ^ (7 / 4 : ℝ) := by
      rw [← Real.rpow_add hP0]; norm_num
    calc _ ≤ (2 * CG * P ^ (13 / 8 : ℝ)) * (2 * CT * (25 * P ^ (1 / 8 : ℝ)) / Real.sqrt Y) :=
          mul_le_mul step5 hA (by positivity) (by positivity)
      _ = 2 * CG * (2 * CT * 25) * (P ^ (13 / 8 : ℝ) * P ^ (1 / 8 : ℝ)) / Real.sqrt Y := by
          ring
      _ = _ := by rw [hpp]
  exact step1.trans (step2.trans (step3.le.trans (step4.trans hfin)))

example : type_of% @S2star_M0_L1 := S2star_M0_L1_of_pieces

end LeanLab.KumchevLiu2007.Prep1122S2starL1

#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.complete_gauss_coprime
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.complete_gauss_gcd
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.gaussS_moebius
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.complete_gauss_le
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.card_divisors_le_rpow
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.gaussS_norm_le
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.arc_eq_Icc
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.arc_localize
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.S2star_norm_le_on_M0
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.T2_arc_integral
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.arcPairs_sum_le
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.log_one_add_cube_le
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.eventually_small
#print axioms LeanLab.KumchevLiu2007.Prep1122S2starL1.S2star_M0_L1_of_pieces
