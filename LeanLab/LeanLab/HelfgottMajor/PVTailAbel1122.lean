import Mathlib
import LeanLab.HelfgottMajor.PV420Split1122
import LeanLab.HelfgottMajor.PVEvenTrunc1122

/-!
Route burst S75, burst-20261122, tag cot-tail. Shared pieces of the truncation error in
Pomerance 2011, Remarks on the Polya-Vinogradov inequality, Integers 11A, Article 19,
the copy at papers/Pomerance2011-Integers11A-A19.pdf, Section 2 Lemma 4 and display 5,
used for the HARD LEAFs `PVEvenTrunc1122.cot_tail` and `PVOddTrunc1122.odd_truncated_large`.

The lab's statements use the cotangent form of the Polya expansion, Frolenkov arXiv 1107.0381
display 12, with a tail H < h < q - H in the dual variable h. Pomerance bounds his tail B_n,
the Fourier tail m > n, by writing it through the Gauss sum, display 7, as a sum over a of
R_n(2πa/q), then Lemma 4: Abel summation |R_n(x)| ≤ 1/((n+1) sin(x/2)) and the cosecant sum
of display 5. The same three steps bound the cotangent tail: the cotangent weight cot(πh/q)
is positive and decreasing on H < h < q/2 and odd under h ↦ q - h, so it plays the role of
1/m in R_n.

Pieces here:
1. `dual_bound`, PROVED: display 7, the Gauss sum duality, ‖∑_{h∈S} χ⁻¹(h) w(h)‖ ≤
   q^(-1/2) ∑_a ‖∑_{h∈S} w(h) e(ah/q)‖, for χ primitive.
2. `tail_cot_sum_zero`, LEAF EASY: the cotangent tail sums to 0, by h ↦ -h.
3. `abel_tail`, LEAF MEDIUM: Lemma 4 first display in cotangent form, the Abel summation bound
   ‖∑_{tail} cot(πh/q) e(bh/q)‖ ≤ 2 cot(π(H+1)/q) / sin(πb/q) for b ≠ 0.
4. `csc_sum_integral`, LEAF MEDIUM: Lemma 4 proof, concavity of csc and its integral.
5. `csc_sum`, PROVED from 4: display 5 as printed.
6. `tail_V_sum`, PROVED from 2, 3: the sum over all b of the tail norms.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVTailAbel1122Aux.Zero
open Real Finset
lemma neg_val_tail {q : ℕ} [NeZero q] (H : ℕ) (h : ZMod q)
    (hh : ¬ (h.val ≤ H ∨ q - H ≤ h.val)) : (-h).val = q - h.val ∧ ¬ ((-h).val ≤ H ∨ q - H ≤ (-h).val) := by
  have hne : h ≠ 0 := by
    rintro rfl; simp at hh
  have hv : (-h).val = q - h.val := by
    rw [ZMod.neg_val, if_neg hne]
  have := ZMod.val_lt h
  refine ⟨hv, ?_⟩
  rw [hv]; omega

theorem tail_cot_sum_zero_proof {q : ℕ} [NeZero q] (H : ℕ) :
    ∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
      (cot (π * h.val / q) : ℂ) = 0 := by
  set S := univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)) with hS
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have key : ∑ h ∈ S, (cot (π * h.val / q) : ℂ) = ∑ h ∈ S, (cot (π * (-h).val / q) : ℂ) := by
    refine (Finset.sum_equiv (Equiv.neg (ZMod q)) ?_ ?_).symm
    · intro i
      simp only [hS, mem_filter, mem_univ, true_and, Equiv.neg_apply]
      constructor
      · intro hi; exact (neg_val_tail H i hi).2
      · intro hi; have := (neg_val_tail H (-i) hi).2; rwa [neg_neg] at this
    · intro i _; simp
  have hodd : ∀ h ∈ S, (cot (π * (-h).val / q) : ℂ) = - (cot (π * h.val / q) : ℂ) := by
    intro h hh
    simp only [hS, mem_filter, mem_univ, true_and] at hh
    obtain ⟨hv, _⟩ := neg_val_tail H h hh
    have hle : h.val ≤ q := (ZMod.val_lt h).le
    rw [hv, Nat.cast_sub hle]
    have : π * ((q : ℝ) - h.val) / q = π - π * h.val / q := by field_simp
    rw [this, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, cos_pi_sub, sin_pi_sub]
    push_cast; ring
  rw [sum_congr rfl hodd, sum_neg_distrib] at key
  have : (2 : ℂ) * ∑ h ∈ S, (cot (π * h.val / q) : ℂ) = 0 := by linear_combination key
  simpa using this
end LeanLab.HelfgottMajor.PVTailAbel1122Aux.Zero

open Real Finset

namespace LeanLab.HelfgottMajor.PVTailAbel1122Aux.Abel

theorem abel_identity (w : ℂ) (d : ℕ → ℝ) (n : ℕ) :
    (w - 1) * ∑ k ∈ range (n + 1), (d k : ℂ) * w ^ k =
      (d n : ℂ) * w ^ (n + 1) - (d 0 : ℂ) +
        ∑ k ∈ range n, ((d k - d (k + 1) : ℝ) : ℂ) * w ^ (k + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    push_cast; ring

theorem abel_bound (w : ℂ) (hw : ‖w‖ = 1) (d : ℕ → ℝ) (n : ℕ)
    (hd : ∀ k < n, d (k + 1) ≤ d k) :
    ‖w - 1‖ * ‖∑ k ∈ range (n + 1), (d k : ℂ) * w ^ k‖ ≤
      |d n| + |d 0| + (d 0 - d n) := by
  rw [← norm_mul, abel_identity]
  have htel : ∑ k ∈ range n, (d k - d (k + 1)) = d 0 - d n := by
    rw [sum_range_sub' d n]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(d n : ℂ) * w ^ (n + 1) - (d 0 : ℂ)‖ ≤ |d n| + |d 0| := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_pow, hw, one_pow, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ‖∑ k ∈ range n, ((d k - d (k + 1) : ℝ) : ℂ) * w ^ (k + 1)‖ ≤ d 0 - d n := by
    rw [← htel]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_pow, hw, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hd k (mem_range.mp hk)])]
  linarith

theorem cot_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < π) : cot y ≤ cot x := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin]
  have sx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith)
  have sy : 0 < sin y := sin_pos_of_pos_of_lt_pi (by linarith) hy
  rw [div_le_div_iff₀ sy sx]
  have : 0 ≤ sin (y - x) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [sin_sub] at this
  nlinarith

end LeanLab.HelfgottMajor.PVTailAbel1122Aux.Abel

namespace LeanLab.HelfgottMajor.PVTailAbel1122
open LeanLab.HelfgottMajor.PVTailAbel1122Aux.Abel

theorem abel_tail_proof {q : ℕ} [NeZero q] (H : ℕ) (hHq : 2 * (H + 1) < q) (b : ZMod q) (hb : b ≠ 0) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ ≤
      2 * cot (π * (H + 1) / q) / sin (π * b.val / q) := by
  set w : ℂ := ZMod.stdAddChar b with hwdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set F : ℕ → ℂ := fun v => (cot (π * v / q) : ℂ) * w ^ v with hF
  have step1 : ∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h) = ∑ v ∈ Ico (H + 1) (q - H), F v := by
    refine sum_nbij (fun h : ZMod q => h.val) ?_ ?_ ?_ ?_
    · intro h hh
      simp only [mem_filter, mem_univ, true_and, not_or, not_le] at hh
      rw [mem_Ico]; omega
    · intro a _ c _ hac; exact ZMod.val_injective q hac
    · intro v hv
      rw [coe_Ico, Set.mem_Ico] at hv
      have hvq : v < q := by omega
      refine ⟨(v : ZMod q), ?_, ?_⟩
      · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_or, not_le,
          ZMod.val_cast_of_lt hvq]
        omega
      · simp only; rw [ZMod.val_cast_of_lt hvq]
    · intro h _
      simp only [hF, hwdef]
      congr 1
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  set n := q - 2 * H - 2 with hn
  set d : ℕ → ℝ := fun k => cot (π * ((H + 1 + k : ℕ) : ℝ) / q) with hd
  have step2 : ∑ v ∈ Ico (H + 1) (q - H), F v =
      w ^ (H + 1) * ∑ k ∈ range (n + 1), (d k : ℂ) * w ^ k := by
    rw [sum_Ico_eq_sum_range, show q - H - (H + 1) = n + 1 by omega, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [hF, hd, pow_add]; ring
  have hw1 : ‖w‖ = 1 := by rw [hwdef, ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  have hbpos : 0 < b.val := by
    rcases Nat.eq_zero_or_pos b.val with h | h
    · exact absurd ((ZMod.val_eq_zero b).mp h) hb
    · exact h
  have hbq : (b.val : ℝ) < q := by exact_mod_cast ZMod.val_lt b
  have hb0 : (0 : ℝ) < b.val := by exact_mod_cast hbpos
  have hs : 0 < sin (π * b.val / q) := by
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hq0]; nlinarith [pi_pos]
  have hwm : ‖w - 1‖ = 2 * sin (π * b.val / q) := by
    rw [hwdef, ZMod.stdAddChar_apply, ZMod.toCircle_apply,
      show 2 * (π : ℂ) * Complex.I * (b.val : ℂ) / (q : ℂ) =
        Complex.I * ((2 * π * b.val / q : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      show 2 * π * (b.val : ℝ) / q / 2 = π * b.val / q by ring, abs_of_pos (by positivity)]
  have hHq' : (2 * ((H : ℝ) + 1)) < q := by exact_mod_cast hHq
  have hd0 : d 0 = cot (π * (H + 1) / q) := by simp [hd]
  have hc : 0 < cot (π * (H + 1) / q) := by
    rw [cot_eq_cos_div_sin]
    have h1 : π * (H + 1) / q < π / 2 := by
      rw [div_lt_iff₀ hq0]; nlinarith [pi_pos]
    apply div_pos
    · exact cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, (by positivity : 0 < π * (H + 1) / q)], h1⟩
    · exact sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hdn : d n = - cot (π * (H + 1) / q) := by
    simp only [hd]
    rw [show H + 1 + n = q - (H + 1) by omega, Nat.cast_sub (by omega)]
    push_cast
    rw [show π * ((q : ℝ) - (H + 1)) / q = π - π * (H + 1) / q by field_simp,
      cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_pi_sub, sin_pi_sub, neg_div]
  have hmono : ∀ k < n, d (k + 1) ≤ d k := by
    intro k hk
    simp only [hd]
    have hk' : ((H + 1 + (k + 1) : ℕ) : ℝ) < q := by exact_mod_cast (show H + 1 + (k + 1) < q by omega)
    apply cot_anti (by positivity)
    · gcongr; omega
    · rw [div_lt_iff₀ hq0]; nlinarith [pi_pos]
  have hab := abel_bound w hw1 d n hmono
  rw [hdn, hd0, abs_neg, abs_of_pos hc, hwm] at hab
  rw [step1, step2, norm_mul, norm_pow, hw1, one_pow, one_mul, le_div_iff₀ hs]
  nlinarith

end LeanLab.HelfgottMajor.PVTailAbel1122

open Real Finset

namespace LeanLab.HelfgottMajor.PVTailAbel1122Aux.Csc

/-- Helper for `csc_sum_integral`, Pomerance 2011 Lemma 4 proof, page 6 first display: an
antiderivative of csc, F(t) = log(1 - cos t) - log(sin t) = log tan(t/2), whose values at
π/(2q) and π - π/(2q) give 2 log((1 + cos(π/(2q)))/sin(π/(2q))). -/
noncomputable def F (t : ℝ) : ℝ := log (1 - cos t) - log (sin t)

lemma hasDerivF {t : ℝ} (h0 : 0 < t) (hπ : t < π) : HasDerivAt F (1 / sin t) t := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi h0 hπ
  have hc : 0 < 1 - cos t := by nlinarith [sin_sq_add_cos_sq t, cos_le_one t]
  have h1 : HasDerivAt (fun y => log (1 - cos y)) (-(-sin t) / (1 - cos t)) t :=
    ((hasDerivAt_cos t).const_sub 1).log hc.ne'
  have h2 : HasDerivAt (fun y => log (sin y)) (cos t / sin t) t :=
    (hasDerivAt_sin t).log hs.ne'
  unfold F
  refine (h1.sub h2).congr_deriv ?_
  rw [neg_neg, div_sub_div _ _ hc.ne' hs.ne', div_eq_div_iff (mul_ne_zero hc.ne' hs.ne') hs.ne']
  linear_combination (sin t) * sin_sq_add_cos_sq t

lemma key_ineq {A B S : ℝ} (hA : 0 < A) (hB : 0 < B) (hS : 0 < S) (h : A * B < S ^ 2) :
    0 < 1 / A + 1 / B - 2 / S := by
  have hk : 2 * A * B < (A + B) * S := by
    by_contra hc
    push Not at hc
    have h0 : 0 ≤ (A + B) * S := by positivity
    have hsq : ((A + B) * S) ^ 2 ≤ (2 * A * B) ^ 2 := pow_le_pow_left₀ h0 hc 2
    have h4 : 4 * A * B ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg (A - B)]
    have h5 : 4 * A * B * S ^ 2 ≤ (A + B) ^ 2 * S ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    have hAB : 0 < A * B := mul_pos hA hB
    have : 4 * (A * B) * S ^ 2 ≤ 4 * (A * B) * (A * B) := by nlinarith
    have : S ^ 2 ≤ A * B := by
      have := le_of_mul_le_mul_left this (by positivity : (0:ℝ) < 4 * (A * B))
      exact this
    linarith
  have : 1 / A + 1 / B - 2 / S = ((A + B) * S - 2 * A * B) / (A * B * S) := by
    field_simp; ring
  rw [this]
  apply div_pos
  · linarith
  · positivity

lemma pointwise {x d : ℝ} (hd : 0 < d) (hdx : d < x) (hxd : x + d < π) :
    2 * d / sin x < F (x + d) - F (x - d) := by
  have hx0 : 0 < x := by linarith
  have hxπ : x < π := by linarith
  have hS : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 hxπ
  set g : ℝ → ℝ := fun s => F (x + s) - F (x - s) - 2 * s / sin x with hg
  have hder : ∀ s ∈ Set.Icc (0:ℝ) d,
      HasDerivAt g (1 / sin (x + s) + 1 / sin (x - s) - 2 / sin x) s := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have h1 : HasDerivAt (fun s => F (x + s)) (1 / sin (x + s)) s :=
      (hasDerivF (by linarith) (by linarith)).comp_const_add x s
    have h2 : HasDerivAt (fun s => F (x - s)) (-(1 / sin (x - s))) s :=
      (hasDerivF (by linarith) (by linarith)).comp_const_sub x s
    have h3 : HasDerivAt (fun s : ℝ => 2 * s / sin x) (2 * 1 / sin x) s :=
      ((hasDerivAt_id s).const_mul 2).div_const (sin x)
    convert (h1.sub h2).sub h3 using 1
    ring
  have hmono : StrictMonoOn g (Set.Icc 0 d) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 d)
    · intro s hs; exact (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Set.Icc (0:ℝ) d := Set.Ioo_subset_Icc_self hs
      rw [(hder s hs').deriv]
      rw [Set.mem_Ioo] at hs
      have hA : 0 < sin (x + s) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hB : 0 < sin (x - s) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hss : 0 < sin s := sin_pos_of_pos_of_lt_pi hs.1 (by linarith)
      apply key_ineq hA hB hS
      rw [sin_add, sin_sub]
      nlinarith [sin_sq_add_cos_sq x, sin_sq_add_cos_sq s]
  have := hmono (Set.left_mem_Icc.2 hd.le) (Set.right_mem_Icc.2 hd.le) hd
  simp only [hg, add_zero, sub_zero, mul_zero, zero_div] at this
  linarith

lemma telescope (H : ℝ → ℝ) (n : ℕ) :
    ∑ a ∈ Icc 1 n, (H a - H ((a:ℝ) - 1)) = H n - H 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast; ring

theorem csc_sum_integral_proof {q : ℕ} (hq : 1 < q) :
    ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q) <
      2 * q / π * log ((1 + cos (π / (2 * q))) / sin (π / (2 * q))) := by
  have hq1 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set d := π / (2 * q) with hd
  have hd0 : 0 < d := by positivity
  have hdpi : d < π := by
    rw [hd, div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hdpi2 : d ≤ π / 4 := by
    rw [hd, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]
  set H : ℝ → ℝ := fun y => F (π * (2 * y + 1) / (2 * q)) with hH
  have hterm : ∀ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q) <
      (q / π) * (H a - H ((a:ℝ) - 1)) := by
    intro a ha
    rw [mem_Icc] at ha
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
    have ha2 : (a : ℝ) ≤ q - 1 := by
      have : a + 1 ≤ q := by omega
      have : (a : ℝ) + 1 ≤ q := by exact_mod_cast this
      linarith
    have hx : d < π * a / q := by
      rw [hd, div_lt_div_iff₀ (by positivity) hq0]
      have := mul_pos pi_pos (by nlinarith : (0:ℝ) < 2 * a * q - q); nlinarith
    have hx2 : π * a / q + d < π := by
      rw [hd, div_add_div _ _ hq0.ne' (by positivity), div_lt_iff₀ (by positivity)]
      have := mul_pos pi_pos (by nlinarith : (0:ℝ) < q * (2 * q - 2 * a - 1)); nlinarith
    have := pointwise hd0 hx hx2
    have e1 : H a = F (π * a / q + d) := by
      simp only [hH, hd]; congr 1; field_simp
    have e2 : H ((a:ℝ) - 1) = F (π * a / q - d) := by
      simp only [hH, hd]; congr 1; field_simp; ring
    rw [e1, e2]
    have hS : 0 < sin (π * a / q) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
    have h2d : 2 * d = π / q := by rw [hd]; field_simp
    rw [h2d] at this
    have e3 : 1 / sin (π * a / q) = (q / π) * (π / q / sin (π * a / q)) := by
      field_simp
    rw [e3]; exact mul_lt_mul_of_pos_left this (by positivity)
  have hne : (Icc 1 (q - 1)).Nonempty := ⟨1, by rw [mem_Icc]; omega⟩
  refine (sum_lt_sum_of_nonempty hne hterm).trans_le (le_of_eq ?_)
  rw [← mul_sum, telescope H (q - 1)]
  have e1 : H ((q - 1 : ℕ) : ℝ) = F (π - d) := by
    simp only [hH, hd]; congr 1; rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring
  have e2 : H 0 = F d := by
    simp only [hH, hd]; congr 1; ring
  rw [e1, e2]
  simp only [F, cos_pi_sub, sin_pi_sub, sub_neg_eq_add]
  have hs : 0 < sin d := sin_pos_of_pos_of_lt_pi hd0 hdpi
  have hc : 0 < 1 - cos d := by nlinarith [sin_sq_add_cos_sq d, cos_le_one d]
  have hc2 : 0 < 1 + cos d := by nlinarith [sin_sq_add_cos_sq d, neg_one_le_cos d]
  have hl : log (1 - cos d) + log (1 + cos d) = 2 * log (sin d) := by
    rw [← log_mul hc.ne' hc2.ne', show (2:ℝ) * log (sin d) = log (sin d ^ 2) by
      rw [log_pow]; norm_num]
    congr 1; nlinarith [sin_sq_add_cos_sq d]
  rw [log_div hc2.ne' hs.ne']
  field_simp
  linarith

end LeanLab.HelfgottMajor.PVTailAbel1122Aux.Csc

namespace LeanLab.HelfgottMajor.PVTailAbel1122

open Real Finset

/-- Pomerance display 7, used in the bound for B_n on page 8: for χ primitive mod q,
`χ⁻¹(h) τ(χ) = ∑_a χ(a) e(ah/q)`, so any twisted sum over a set S of residues is at most
q^(-1/2) times the sum over a of the untwisted exponential sums. PROVED. -/
theorem dual_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (S : Finset (ZMod q)) (w : ZMod q → ℂ) :
    ‖∑ h ∈ S, χ⁻¹ h * w h‖ ≤
      1 / sqrt q * ∑ a : ZMod q, ‖∑ h ∈ S, w h * ZMod.stdAddChar (a * h)‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  have hg := LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ
  have key : (∑ h ∈ S, χ⁻¹ h * w h) * gaussSum χ ZMod.stdAddChar =
      ∑ a : ZMod q, χ a * ∑ h ∈ S, w h * ZMod.stdAddChar (a * h) := by
    rw [sum_mul]
    have : ∀ h ∈ S, χ⁻¹ h * w h * gaussSum χ ZMod.stdAddChar =
        ∑ a : ZMod q, w h * (χ a * ZMod.stdAddChar (a * h)) := by
      intro h _
      rw [mul_comm (χ⁻¹ h) (w h), mul_assoc, LeanLab.HelfgottMajor.PV420Split1122.gauss_twist hχ h,
        mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_comm h a]
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    ring
  have hn := congrArg norm key
  rw [norm_mul, hg] at hn
  have hle : ‖∑ a : ZMod q, χ a * ∑ h ∈ S, w h * ZMod.stdAddChar (a * h)‖ ≤
      ∑ a : ZMod q, ‖∑ h ∈ S, w h * ZMod.stdAddChar (a * h)‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    have := DirichletCharacter.norm_le_one χ a
    calc ‖χ a‖ * ‖∑ h ∈ S, w h * ZMod.stdAddChar (a * h)‖ ≤
        1 * ‖∑ h ∈ S, w h * ZMod.stdAddChar (a * h)‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  rw [← hn] at hle
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs]
  exact hle

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Lemma 4 proof, the oddness R_n(2π - x) = -R_n(x), in cotangent form:
the tail H < h < q - H of the cotangent weights sums to 0, since h ↦ -h preserves the tail
and cot(π - y) = -cot y. Class EASY. -/
theorem tail_cot_sum_zero {q : ℕ} [NeZero q] (H : ℕ) :
    ∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
      (cot (π * h.val / q) : ℂ) = 0 := by
  apply LeanLab.HelfgottMajor.PVTailAbel1122Aux.Zero.tail_cot_sum_zero_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Lemma 4, first display of the proof, |R_n(x)| ≤ 1/((n+1) sin(x/2)),
in cotangent form: for b ≠ 0 and 2(H+1) < q, pairing h with q - h writes the tail as
2i ∑_{H<h<q/2} cot(πh/q) sin(2πbh/q); cot(πh/q) is positive and decreasing there and the partial
sums of sin(2πbh/q) are at most 1/sin(πb/q) in absolute value, so Abel summation gives the bound.
Class MEDIUM. -/
theorem abel_tail {q : ℕ} [NeZero q] (H : ℕ) (hHq : 2 * (H + 1) < q) (b : ZMod q) (hb : b ≠ 0) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ ≤
      2 * cot (π * (H + 1) / q) / sin (π * b.val / q) := by
  apply abel_tail_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Lemma 4 proof, page 5 and the first display of page 6: csc is
concave up on (0, π), so csc(πa/q) < (q/π) ∫ csc over [π(a-1/2)/q, π(a+1/2)/q], and the
integral over [π/(2q), π - π/(2q)] is 2 log((1 + cos(π/(2q)))/sin(π/(2q))). Class MEDIUM. -/
theorem csc_sum_integral {q : ℕ} (hq : 1 < q) :
    ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q) <
      2 * q / π * log ((1 + cos (π / (2 * q))) / sin (π / (2 * q))) := by
  apply LeanLab.HelfgottMajor.PVTailAbel1122Aux.Csc.csc_sum_integral_proof <;> assumption

/-- Pomerance 2011 display 5: ∑_{a=1}^{q-1} 1/sin(πa/q) < (2q/π)(log q + log(4/π) + π²/(12q²)),
from `csc_sum_integral` with cos t < 1, sin t > t - t³/6 and log(1/(1-t)) < 2t for 0 < t < 1/2.
PROVED from the LEAF `csc_sum_integral`. -/
theorem csc_sum {q : ℕ} (hq : 1 < q) :
    ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q) <
      2 * q / π * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) := by
  have h1 := csc_sum_integral hq
  have hq1 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set t := π / (2 * q) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ π / 4 := by
    rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]
  have hpi4 : π / 4 < 1 := by linarith [pi_lt_d2]
  have ht1' : t < 1 := lt_of_le_of_lt ht1 hpi4
  have hsin_lb : t - t ^ 3 / 6 < sin t := by
    exact Real.sin_gt_sub_cube ht0
  have hu : 0 < 1 - t ^ 2 / 6 := by nlinarith
  have hlow : 0 < t - t ^ 3 / 6 := by nlinarith
  have hsin0 : 0 < sin t := lt_trans hlow hsin_lb
  have hcos : cos t ≤ 1 := Real.cos_le_one t
  have hnum : 0 < 1 + cos t := by
    have := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩ (x := t)
    linarith
  have hratio : (1 + cos t) / sin t < 2 / (t - t ^ 3 / 6) := by
    rw [div_lt_div_iff₀ hsin0 hlow]
    nlinarith
  have hlog1 : log ((1 + cos t) / sin t) < log (2 / (t - t ^ 3 / 6)) :=
    log_lt_log (div_pos hnum hsin0) hratio
  have hsplit : 2 / (t - t ^ 3 / 6) = (4 * q / π) * (1 / (1 - t ^ 2 / 6)) := by
    rw [ht]; field_simp; ring
  have hlog2 : log (2 / (t - t ^ 3 / 6)) = log q + log (4 / π) + log (1 / (1 - t ^ 2 / 6)) := by
    rw [hsplit, log_mul (by positivity) (by positivity),
      show 4 * (q : ℝ) / π = q * (4 / π) by ring, log_mul (by positivity) (by positivity)]
  have hs : t ^ 2 / 6 < 1 / 2 := by nlinarith
  have hs0 : 0 < t ^ 2 / 6 := by positivity
  have hlog3 : log (1 / (1 - t ^ 2 / 6)) < 2 * (t ^ 2 / 6) := by
    -- log(1/(1-s)) < log(1+2s) < 2s for 0 < s < 1/2
    have hpos : 0 < 1 - t ^ 2 / 6 := hu
    have hA : 1 / (1 - t ^ 2 / 6) < 1 + 2 * (t ^ 2 / 6) := by
      rw [div_lt_iff₀ hpos]; nlinarith
    have hB : log (1 / (1 - t ^ 2 / 6)) < log (1 + 2 * (t ^ 2 / 6)) :=
      log_lt_log (by positivity) hA
    have hC : log (1 + 2 * (t ^ 2 / 6)) < 2 * (t ^ 2 / 6) := by
      have := Real.log_lt_sub_one_of_pos (show 0 < 1 + 2 * (t ^ 2 / 6) by positivity)
        (by linarith)
      linarith
    linarith
  have hlast : 2 * (t ^ 2 / 6) = π ^ 2 / (12 * q ^ 2) := by rw [ht]; field_simp; ring
  have hc : 0 < 2 * (q : ℝ) / π := by positivity
  calc ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q) <
      2 * q / π * log ((1 + cos (π / (2 * q))) / sin (π / (2 * q))) := h1
    _ ≤ 2 * q / π * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      rw [← ht]
      linarith

/-- The sum over all b of the tail norms, Pomerance page 8, the step from Lemma 4 to the bound
for |B_n|: the b = 0 term vanishes by `tail_cot_sum_zero`, every other term is bounded by
`abel_tail`, and b ↦ b.val runs over 1, ..., q - 1. PROVED from the two LEAFs. -/
theorem tail_V_sum {q : ℕ} [NeZero q] (H : ℕ) (hHq : 2 * (H + 1) < q) :
    ∑ b : ZMod q, ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ ≤
      2 * cot (π * (H + 1) / q) * ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q) := by
  set V : ZMod q → ℝ := fun b => ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ with hV
  have h0 : V 0 = 0 := by
    show ‖_‖ = 0
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [tail_cot_sum_zero H, norm_zero]
  have hsplit : ∑ b : ZMod q, V b = V 0 + ∑ b ∈ univ.erase (0 : ZMod q), V b := by
    rw [add_sum_erase _ _ (mem_univ _)]
  rw [hsplit, h0, zero_add, mul_sum]
  have hre : ∑ b ∈ univ.erase (0 : ZMod q), 2 * cot (π * (H + 1) / q) / sin (π * b.val / q) =
      ∑ a ∈ Icc 1 (q - 1), 2 * cot (π * (H + 1) / q) * (1 / sin (π * a / q)) := by
    refine sum_nbij (fun b : ZMod q => b.val) ?_ ?_ ?_ ?_
    · intro b hb
      rw [mem_erase] at hb
      have h1 := ZMod.val_lt b
      have h2 : b.val ≠ 0 := by rw [ZMod.val_ne_zero]; exact hb.1
      rw [mem_Icc]; omega
    · intro a _ b _ hab; exact ZMod.val_injective q hab
    · intro v hv
      rw [coe_Icc, Set.mem_Icc] at hv
      have hvq : v < q := by omega
      refine ⟨(v : ZMod q), ?_, ?_⟩
      · simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
          true_and]
        intro h0
        have := congrArg ZMod.val h0
        rw [ZMod.val_cast_of_lt hvq, ZMod.val_zero] at this
        omega
      · simp only; rw [ZMod.val_cast_of_lt hvq]
    · intro b _; ring
  rw [← hre]
  refine sum_le_sum fun b hb => ?_
  exact abel_tail H hHq b (mem_erase.mp hb).1

end LeanLab.HelfgottMajor.PVTailAbel1122

#print axioms LeanLab.HelfgottMajor.PVTailAbel1122.dual_bound
#print axioms LeanLab.HelfgottMajor.PVTailAbel1122.tail_cot_sum_zero
#print axioms LeanLab.HelfgottMajor.PVTailAbel1122.abel_tail
#print axioms LeanLab.HelfgottMajor.PVTailAbel1122.csc_sum_integral
#print axioms LeanLab.HelfgottMajor.PVTailAbel1122.csc_sum
#print axioms LeanLab.HelfgottMajor.PVTailAbel1122.tail_V_sum
