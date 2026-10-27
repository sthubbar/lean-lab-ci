/-
Lemma 3.8 for j = 2, pages 14 and 15 of arXiv 0801.0130.
The smooth tail and the coefficient mean square bound remain CITED inputs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp129
import LeanLab.KumchevLiu2007.Decomp1534b

namespace LeanLab.KumchevLiu2007.Task129b

open Real Complex LeanLab.KumchevLiu2007 Task129
open U1534
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The finite interval of integers in Lemma 3.8 on page 14. -/
noncomputable def intervalNumbers (x y : ℝ) : Finset ℕ := Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊

/-- The j = 2 product in page 13 display 45. Higher prime powers vanish
because A2 contains the Moebius function. -/
noncomputable def product2 (n : ℕ) (Q : ℝ) : ℂ :=
  ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)

/-- The smooth number indicator Psi of page 4 display 11. -/
noncomputable def smoothWeight (q : ℕ) (Q : ℝ) : ℝ :=
  if ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q then 1 else 0

/-- The tail after display 50 on page 14 with the coefficient obtained by
subtracting the product expansion from S2. This coefficient is minus Psi. -/
noncomputable def tail2 (n : ℕ) (P Q0 Q : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊, -(smoothWeight q Q : ℂ) * U1534.A2 n q

/-- CITED. Lemma 3.8 for j = 2, page 14 display 49. Positive P is the
implicit positive cutoff convention. The complex norm expresses the square
of the real valued difference in the paper. -/
def lemma38_two : Prop :=
  ∀ A ε : ℝ, 2 ≤ A → 0 < ε → ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖series2 n P - product2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A)

/-- LEAF. Page 14 display 50 and the smooth tail estimate immediately below
it, converted to a mean square error. This requires Lemma 3.5, cited there
from Tenenbaum Section III.5, and the coefficient bound of display 47. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  sorry

/-- LEAF. Pages 14 and 15 display 51. Expand the tail square into diagonal
and off diagonal terms. Display 47 bounds the diagonal. The orthogonality
property v on page 13 bounds the off diagonal. Those coefficient properties
are cited from Schwarz Section 2 and Section 3 in the paper. -/
theorem tail_mean_square_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  sorry

/-- LEAF. Page 14 after display 50. The square of a sum is at most twice
the sum of the squares, summed over a finite set. -/
theorem mean_square_add {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    (∑ n ∈ s, ‖f n + g n‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖f n‖ ^ 2) + 2 * (∑ n ∈ s, ‖g n‖ ^ 2) := by
  calc _ ≤ ∑ n ∈ s, (2 * ‖f n‖ ^ 2 + 2 * ‖g n‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        have hsq : ‖f n + g n‖ ^ 2 ≤ (‖f n‖ + ‖g n‖) ^ 2 := by
          gcongr
          exact norm_add_le _ _
        nlinarith [sq_nonneg (‖f n‖ - ‖g n‖)]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Lemma 3.8 for j = 2 assembled from the two analytic inputs.
The assembly has no sorry of its own. -/
theorem lemma38_from_leaves : lemma38_two := by
  intro A ε hA hε
  obtain ⟨Ce, Xe, hCe, hXe, he⟩ := truncation_input A ε hA hε
  obtain ⟨Ct, Xt, hCt, hXt, ht⟩ := tail_mean_square_input A ε hA hε
  refine ⟨2 * (Ce + Ct), max Xe Xt, by positivity,
    le_trans hXe (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxe : Xe ≤ x := le_trans (le_max_left _ _) hx
  have hxt : Xt ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ x := hXe.trans hxe
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hy
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have he' := he x y P Q hxe hy hyx hP hPQ hQ
  have ht' := ht x y P Q hxt hy hyx hP hPQ hQ
  have hs := mean_square_add (intervalNumbers x y)
    (fun n => tail2 n P (y ^ (1 / 3 : ℝ)) Q)
    (fun n => (series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q)
  simp only [add_sub_cancel] at hs
  have hmain : 0 ≤ y / P * Real.log x := by positivity
  have herr : Ce * (y / Real.log x ^ A) ≤
      Ce * (y / P * Real.log x + y / Real.log x ^ A) := by
    nlinarith
  calc _ ≤ 2 * (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) +
      2 * (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) := hs
    _ ≤ 2 * (Ct * (y / P * Real.log x + y / Real.log x ^ A)) +
      2 * (Ce * (y / Real.log x ^ A)) := by linarith
    _ ≤ 2 * (Ce + Ct) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

/-- Page 13 display 45. The Moebius factor kills every nonsquarefree modulus. -/
theorem A2_eq_zero_of_not_squarefree (n q : ℕ) (hq : ¬ Squarefree q) : U1534.A2 n q = 0 := by
  simp [U1534.A2, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

/-- Page 13 property v. Each coefficient is periodic in n with period q. -/
theorem A2_periodic (q : ℕ) : Function.Periodic (fun n : ℕ => U1534.A2 n q) q := by
  intro n
  by_cases hq : q = 0
  · subst q
    rfl
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold U1534.A2
  refine congrArg (fun z : ℂ => ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)^2 * z) ?_
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun z : ℂ => U1534.gaussS q a * z)
  unfold U1534.ee
  have heq : 2 * (Real.pi : ℂ) * I * ↑(-((a * (n + q) : ℕ) : ℝ) / q) =
      2 * (Real.pi : ℂ) * I * ↑(-((a * n : ℕ) : ℝ) / q) +
      ((-(a : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    field_simp
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Page 13 property v, over one full period indexed from zero.
Distinct moduli have orthogonal coefficients. -/
theorem A2_orthogonal (q r : ℕ) (hqr : q ≠ r) :
    ∑ n ∈ Finset.range (q * r), U1534.A2 n q * U1534.A2 n r = 0 := by
  by_cases hq : q = 0
  · subst q; simp
  by_cases hr : r = 0
  · subst r; simp
  have hN : q * r ≠ 0 := Nat.mul_ne_zero hq hr
  have : NeZero (q * r) := ⟨hN⟩
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have sum_range (f : ZMod (q * r) → ℂ) :
      ∑ n ∈ Finset.range (q * r), f (n : ZMod (q * r)) = ∑ n : ZMod (q * r), f n := by
    apply Finset.sum_bij (s := Finset.range (q*r))
      (t := (Finset.univ : Finset (ZMod (q*r)))) (fun a _ => (a : ZMod (q*r)))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have cross (a b : ℕ) (ha : a.Coprime q) (hb : b.Coprime r) :
      ∑ n ∈ Finset.range (q*r), ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r) = 0 := by
    have hfreq : (-((a*r+b*q : ℕ) : ZMod (q*r))) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff (a*r+b*q) (q*r)).mp (neg_eq_zero.mp h)
      have hqd : q ∣ a*r+b*q := dvd_trans (dvd_mul_right q r) hd
      have hrd : r ∣ a*r+b*q := dvd_trans (dvd_mul_left r q) hd
      have hqd' : q ∣ a*r := (Nat.dvd_add_iff_left (dvd_mul_left q b)).mpr hqd
      have hrd' : r ∣ b*q := (Nat.dvd_add_iff_right (dvd_mul_left r a)).mpr hrd
      exact hqr (Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hqd')
        (hb.symm.dvd_of_dvd_mul_left hrd'))
    have heq (n : ℕ) : ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r) =
        ZMod.stdAddChar ((n : ZMod (q*r)) * (-((a*r+b*q : ℕ) : ZMod (q*r)))) := by
      have hcast : (n : ZMod (q*r)) * (-((a*r+b*q : ℕ) : ZMod (q*r))) =
          (((-((n*(a*r+b*q) : ℕ) : ℤ)) : ℤ) : ZMod (q*r)) := by push_cast; ring
      rw [hcast, ZMod.stdAddChar_coe]
      unfold ee
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    simp_rw [heq]
    rw [sum_range (fun n => ZMod.stdAddChar (n * (-((a*r+b*q : ℕ) : ZMod (q*r)))))]
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := q*r))
      (-((a*r+b*q : ℕ) : ZMod (q*r))) (ZMod.isPrimitive_stdAddChar (q*r))
    simpa only [ite_eq_right hfreq, Nat.cast_zero] using hs
  unfold A2
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have hca := (Finset.mem_filter.mp ha).2
  have hcb := (Finset.mem_filter.mp hb).2
  have hs := cross a b hca hcb
  have heq (n : ℕ) :
      (((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)^2 *
        (gaussS q a * ee (-((a*n : ℕ) : ℝ)/q))) *
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) / (Nat.totient r : ℂ)^2 *
        (gaussS r b * ee (-((b*n : ℕ) : ℝ)/r))) =
      ((((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)^2 * gaussS q a) *
        (((ArithmeticFunction.moebius r : ℤ) : ℂ) / (Nat.totient r : ℂ)^2 * gaussS r b)) *
        (ee (-((a*n : ℕ) : ℝ)/q) * ee (-((b*n : ℕ) : ℝ)/r)) := by ring
  simp_rw [heq]
  rw [← Finset.mul_sum, hs, mul_zero]

/-- Page 15 off diagonal estimate after display 51. A periodic function
with zero mean has interval sums bounded by two full absolute period sums. -/
theorem periodic_zero_mean_interval (f : ℕ → ℂ) {T : ℕ} (hT : 0 < T)
    (hf : Function.Periodic f T) (hs : ∑ i ∈ Finset.range T, f i = 0) (a b : ℕ) :
    ‖∑ i ∈ Finset.Ico a b, f i‖ ≤ 2 * ∑ i ∈ Finset.range T, ‖f i‖ := by
  have hp : Function.Periodic (fun N => ∑ i ∈ Finset.range N, f i) T := by
    intro N
    change (∑ i ∈ Finset.range (N + T), f i) = ∑ i ∈ Finset.range N, f i
    induction N with
    | zero => simpa using hs
    | succ N ih =>
      rw [show N + 1 + T = (N + T) + 1 by omega, Finset.sum_range_succ, hf N, ih,
        Finset.sum_range_succ]
  have hprefix (N : ℕ) : ‖∑ i ∈ Finset.range N, f i‖ ≤ ∑ i ∈ Finset.range T, ‖f i‖ := by
    rw [← hp.map_mod_nat N]
    calc _ ≤ ∑ i ∈ Finset.range (N % T), ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range T, ‖f i‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.mod_lt N hT).le
        · intro i hi hi'; exact norm_nonneg _
  by_cases hab : a ≤ b
  · rw [Finset.sum_Ico_eq_sub _ hab]
    calc _ ≤ ‖∑ i ∈ Finset.range b, f i‖ + ‖∑ i ∈ Finset.range a, f i‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hprefix a, hprefix b]
  · have hempty : Finset.Ico a b = ∅ := Finset.Ico_eq_empty_of_le (by omega : b ≤ a)
    rw [hempty, Finset.sum_empty, norm_zero]
    positivity

/-- Page 15 after display 51. Orthogonality bounds an incomplete interval
by twice the absolute sum over a full joint period. -/
theorem A2_interval_bound {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, A2 n q * A2 n r‖ ≤
      2 * ∑ n ∈ Finset.range (q * r), ‖A2 n q * A2 n r‖ := by
  have hq' : Function.Periodic (fun n => A2 n q) (q * r) := by
    simpa [Nat.mul_comm] using (A2_periodic q).nat_mul r
  have hr' : Function.Periodic (fun n => A2 n r) (q * r) := by
    simpa using (A2_periodic r).nat_mul q
  exact periodic_zero_mean_interval _ (Nat.mul_pos hq hr) (hq'.mul hr')
    (A2_orthogonal q r hqr) a b

/-- Page 13 display 45 and page 14 display 46, computed by additive
character orthogonality. The nonzero square root count determines A2 at a prime. -/
theorem A2_prime_root_count (p : ℕ) [Fact p.Prime] (n : ℕ) :
    A2 n p = ((p : ℂ) - 1 - (p : ℂ) *
      (((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card : ℂ)) /
      ((p : ℂ) - 1) ^ 2 := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have std_int (a : ℤ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    rw [ZMod.stdAddChar_coe]
    unfold ee
    congr 1
    push_cast
    ring
  have std_nat (a : ℕ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    simpa using std_int (a : ℤ)
  have sum_range (f : ZMod p → ℂ) :
      ∑ a ∈ Finset.range p, f (a : ZMod p) = ∑ a : ZMod p, f a := by
    apply Finset.sum_bij (s := Finset.range p) (t := (Finset.univ : Finset (ZMod p))) (fun a _ => (a : ZMod p))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have coprime_iff (a : ℕ) : Nat.Coprime a p ↔ (a : ZMod p) ≠ 0 := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, ne_eq, ZMod.natCast_eq_zero_iff]
  have filtered (f : ZMod p → ℂ) :
      ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p), f (a : ZMod p) =
      ∑ a ∈ (Finset.univ.erase (0 : ZMod p)), f a := by
    rw [Finset.sum_filter]
    simp_rw [coprime_iff]
    rw [sum_range (fun a => if a ≠ 0 then f a else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  have std_neg (a : ℕ) : ee (-((a * n : ℕ) : ℝ) / p) =
      ZMod.stdAddChar (-((a : ZMod p) * (n : ZMod p))) := by
    have heq : -((a * n : ℕ) : ℝ) / p = ((-((a * n : ℕ) : ℤ) : ℤ) : ℝ) / p := by
      push_cast; ring
    rw [heq, std_int]
    push_cast
    rfl
  have gauss_eq (a : ℕ) : gaussS p a * ee (-((a*n : ℕ) : ℝ)/p) =
      ∑ x ∈ Finset.univ.erase (0 : ZMod p),
        ZMod.stdAddChar ((a : ZMod p) * (x ^ 2 - (n : ZMod p))) := by
    rw [std_neg]
    unfold gaussS
    simp_rw [std_nat, Nat.cast_mul, Nat.cast_pow]
    rw [filtered (fun x => ZMod.stdAddChar ((a : ZMod p) * x ^ 2)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hchar (t : ZMod p) :
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * t) =
        if t = 0 then (p : ℂ) - 1 else -1 := by
    have ht := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) t
      (ZMod.isPrimitive_stdAddChar p)
    have hs := Finset.sum_erase_add (s := Finset.univ)
      (f := fun a : ZMod p => ZMod.stdAddChar (a * t)) (Finset.mem_univ 0)
    simp only [zero_mul, AddChar.map_zero_eq_one] at hs
    rw [ht, ZMod.card] at hs
    by_cases ht0 : t = 0
    · simp only [ht0, ite_true] at hs ⊢
      linear_combination hs
    · simp only [ht0, ite_false, Nat.cast_zero] at hs ⊢
      linear_combination hs
  let s := Finset.univ.erase (0 : ZMod p)
  let R := s.filter (fun x => x ^ 2 = (n : ZMod p))
  have hg : ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
      gaussS p a * ee (-((a*n : ℕ) : ℝ)/p) =
      (p : ℂ) * (R.card : ℂ) - ((p : ℂ) - 1) := by
    simp_rw [gauss_eq]
    rw [filtered (fun a => ∑ x ∈ Finset.univ.erase (0 : ZMod p),
      ZMod.stdAddChar (a * (x ^ 2 - (n : ZMod p)))), Finset.sum_comm]
    simp_rw [hchar, sub_eq_zero]
    have heq (x : ZMod p) : (if x ^ 2 = (n : ZMod p) then (p : ℂ) - 1 else -1) =
        (p : ℂ) * (if x ^ 2 = (n : ZMod p) then 1 else 0) - 1 := by
      split_ifs <;> ring
    simp_rw [heq, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hR : (∑ x ∈ s, if x ^ 2 = (n : ZMod p) then (1 : ℂ) else 0) = R.card := by
      simp [R]
    change (p : ℂ) * (∑ x ∈ s, if x ^ 2 = (n : ZMod p) then (1 : ℂ) else 0) -
      (∑ x ∈ s, (1 : ℂ)) = _
    rw [hR]
    simp [s, ZMod.card, Nat.cast_sub hp.one_le]
  unfold A2
  rw [hg, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  norm_num only [Int.cast_neg, Int.cast_one, Nat.cast_sub hp.one_le, Nat.cast_one]
  change -1 / ((p : ℂ) - 1)^2 * ((p : ℂ) * (R.card : ℂ) - ((p : ℂ) - 1)) =
    ((p : ℂ) - 1 - (p : ℂ) * (R.card : ℂ)) / ((p : ℂ) - 1)^2
  ring

/-- Page 14 display 46. The root count used in the prime factor formula
is at most two, by the degree of X squared minus n. -/
theorem nonzero_square_roots_le_two (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card ≤ 2 := by
  let f : Polynomial (ZMod p) := Polynomial.X ^ 2 - Polynomial.C (n : ZMod p)
  have hf : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) _
  have hsub : ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).val ⊆ f.roots := by
    intro x hx
    apply (Polynomial.mem_roots hf).mpr
    have heq := (Finset.mem_filter.mp hx).2
    simpa [f] using sub_eq_zero.mpr heq
  have hc := Polynomial.card_le_degree_of_subset_roots hsub
  simpa only [f, Polynomial.natDegree_X_pow_sub_C] using hc

/-- Page 13 property iii and page 14 display 46. The prime factor is
strictly greater than minus one at every prime at least five. -/
theorem A2_prime_re_gt_neg_one (p : ℕ) [Fact p.Prime] (n : ℕ) (h5 : 5 ≤ p) :
    -1 < (A2 n p).re := by
  let R := (Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))
  have hp : p.Prime := Fact.out
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have hR : (R.card : ℝ) ≤ 2 := by exact_mod_cast nonzero_square_roots_le_two p n
  have heq : A2 n p =
      ((((p : ℝ) - 1 - (p : ℝ) * (R.card : ℝ)) / ((p : ℝ) - 1)^2 : ℝ) : ℂ) := by
    rw [A2_prime_root_count]
    push_cast
    rfl
  rw [heq, Complex.ofReal_re]
  have hd : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  rw [lt_div_iff₀ hd]
  have hm : (p : ℝ) * (R.card : ℝ) ≤ (p : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  have hp3 : 0 < (p : ℝ) * ((p : ℝ) - 3) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- Page 14 display 47 at a prime, with an explicit rational upper bound
from the root count formula. -/
theorem A2_prime_norm_bound (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖A2 n p‖ ≤ ((p : ℝ) + 1) / ((p : ℝ) - 1)^2 := by
  let R := (Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))
  have hp : p.Prime := Fact.out
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hR : (R.card : ℝ) ≤ 2 := by exact_mod_cast nonzero_square_roots_le_two p n
  have heq : A2 n p =
      ((((p : ℝ) - 1 - (p : ℝ) * (R.card : ℝ)) / ((p : ℝ) - 1)^2 : ℝ) : ℂ) := by
    rw [A2_prime_root_count]
    push_cast
    rfl
  have hd : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  have hm : (p : ℝ) * (R.card : ℝ) ≤ (p : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  have hn : 0 ≤ (p : ℝ) * (R.card : ℝ) := by positivity
  have habs : |(p : ℝ) - 1 - (p : ℝ) * (R.card : ℝ)| ≤ (p : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right habs hd.le

/-- Page 13 property iii. Every admissible n has a positive prime local
factor, including the primes two and three. -/
theorem A2_local_factor_positive {n p : ℕ} (hn : InH2 n) (hp : p.Prime) :
    0 < (1 + A2 n p).re := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · subst p
    rw [A2_two_even (by have := hn.2; omega)]
    norm_num
  by_cases h3 : p = 3
  · subst p
    rw [A2_three_ne_one hn.1]
    norm_num
  have hlarge := A2_prime_re_gt_neg_one p n (five_le_of_prime hp h2 h3)
  simpa only [Complex.add_re, Complex.one_re] using (by linarith : (0 : ℝ) < 1 + (A2 n p).re)

/-- Page 14 display 47 at a prime, with an explicit error constant. -/
theorem A2_prime_norm_le_inv_add (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖A2 n p‖ ≤ 1 / (p : ℝ) + 6 / (p : ℝ)^2 := by
  have hp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst p
    by_cases hn : n % 2 = 0
    · rw [A2_two_even hn]; norm_num
    · rw [A2_two_odd (by omega)]; norm_num
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  apply (A2_prime_norm_bound p n).trans
  have heq : 1 / (p : ℝ) + 6 / (p : ℝ)^2 = ((p : ℝ) + 6) / (p : ℝ)^2 := by
    field_simp
  rw [heq, div_le_div_iff₀ hd (by positivity : 0 < (p : ℝ)^2)]
  have hh : 0 ≤ ((p : ℝ) - 3) * (3 * (p : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Page 13 display 45, evaluated using Mathlib's Legendre root count.
The relation to the printed sign in page 14 display 46 remains a QUESTION. -/
theorem A2_prime_legendre_exact (p : ℕ) [Fact p.Prime] (n : ℕ)
    (hp2 : p ≠ 2) (hn : ¬ p ∣ n) :
    A2 n p = -((p : ℂ) * (legendreSym p (n : ℤ) : ℂ) + 1) / ((p : ℂ) - 1)^2 := by
  have hnZ : (n : ZMod p) ≠ 0 := by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using hn
  let R := (Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))
  have hRset : R = {x : ZMod p | x ^ 2 = (n : ℤ)}.toFinset := by
    ext x
    simp only [R, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      Set.mem_toFinset, Int.cast_natCast]
    constructor
    · exact And.right
    · intro hx
      refine ⟨?_, hx⟩
      intro hx0
      subst x
      exact hnZ (by simpa using hx.symm)
  have hR : (R.card : ℤ) = legendreSym p (n : ℤ) + 1 := by
    rw [hRset]
    exact legendreSym.card_sqrts p hp2 (n : ℤ)
  have hRC : (R.card : ℂ) = (legendreSym p (n : ℤ) : ℂ) + 1 := by exact_mod_cast hR
  rw [A2_prime_root_count]
  change ((p : ℂ) - 1 - (p : ℂ) * (R.card : ℂ)) / ((p : ℂ) - 1)^2 = _
  rw [hRC]
  ring

end LeanLab.KumchevLiu2007.Task129b
