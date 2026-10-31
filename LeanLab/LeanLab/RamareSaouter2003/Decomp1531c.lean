import Mathlib
import LeanLab.RamareSaouter2003.Theorem3Smooth
import LeanLab.RamareSaouter2003.MuStarUpper
import LeanLab.RamareSaouter2003.Stirling126

/-!
# Ramare-Saouter 2003, Sections 5 and 6 and a step toward (11)

Unit U-1531, run 20261026T0004Z-24325, DECOMPOSE. AI wrote this Lean code, Claude, checked only
by the Lean kernel. Binary Goldbach is OPEN.

LEAF lemmas for the analytic bookkeeping of Section 5, the proof of the asymptotic (2) on
pp. 22 and 23, of Section 6, the result under RH on pp. 23 to 25, of the Stirling bound in (21)
on p. 21, and of the split of `psi - theta` behind the lower half of (11) on p. 19.

Assemblies, with real proofs and no sorry of their own, CONDITIONAL ON the leaves:
`v_le_gauss`, (25) to (27); `w_fm_le`, the bound `w(f_m, a) <= e^(-4b^2)/(2b)` of p. 23 for
`a = 1/2 - b/√m`; `w_fm_le_sixteenth`, the case `b = 1`; `section6_interval`, the last
inequality of the list on p. 24 from Lemma 7; `twoN_le_section6`, the hypothesis
`2N(T) <= alpha1 √Y` of Section 6 from the Lemma 1 shape bound for `N(T)`.
-/

namespace LeanLab.RamareSaouter2003.Decomp1531c

open LeanLab.RamareSaouter2003.Smooth Set Chebyshev

/-- LEAF. Unit U-1531. For `a` in `[0, 1/2]`, `v(f_m, a)` equals the integral of
`(1 - h^2)^m` over `[1 - 2a, 1]`, by the symmetry of `f_m` and `t = (1 - h)/2`; p. 23, (25). -/
theorem v_fm_eq (m : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    v (fm m) a = ∫ h in (1 - 2 * a)..1, (1 - h ^ 2) ^ m := by
  have hs := intervalIntegral.integral_comp_sub_mul (fm m)
    (a := (0 : ℝ)) (b := a) (c := (1 : ℝ)) (by norm_num) 1
  simp only [one_mul, sub_zero, inv_one, one_smul, fm_symm] at hs
  have hc := intervalIntegral.integral_comp_sub_mul
    (fun h : ℝ => (1 - h ^ 2) ^ m) (a := (0 : ℝ)) (b := a)
    (c := (2 : ℝ)) (by norm_num) 1
  have he : (fun t : ℝ => (1 - (1 - 2 * t) ^ 2) ^ m) = fm m := by
    funext t
    unfold fm
    congr 1
    ring
  rw [he] at hc
  simp only [mul_zero, sub_zero, smul_eq_mul] at hc
  unfold v
  linarith

/-- LEAF. Unit U-1531. For `h` in `[0, 1]`, `(1 - h^2)^m <= e^(-m h^2)`; p. 23, (27). -/
theorem one_sub_sq_pow_le_exp (m : ℕ) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    (1 - h ^ 2) ^ m ≤ Real.exp (-(m * h ^ 2)) := by
  have hbase : 0 ≤ 1 - h ^ 2 := by nlinarith
  calc
    (1 - h ^ 2) ^ m ≤ (Real.exp (-(h ^ 2))) ^ m :=
      pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg _ ) _
    _ = Real.exp (-(m * h ^ 2)) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- LEAF. Unit U-1531. Gaussian tail: for `m > 0` and `0 < c <= 1`, the integral of
`e^(-m h^2)` over `[c, 1]` is at most `e^(-m c^2)/(2 m c)`; p. 23, (27). -/
theorem gauss_tail {m : ℝ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ h in c..1, Real.exp (-(m * h ^ 2))) ≤ Real.exp (-(m * c ^ 2)) / (2 * m * c) := by
  have hden : 0 < 2 * m * c := by positivity
  have hd (t : ℝ) : HasDerivAt
      (fun h : ℝ => -Real.exp (-(m * h ^ 2)) / (2 * m * c))
      (t / c * Real.exp (-(m * t ^ 2))) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul m).neg.exp.neg.div_const (2 * m * c) using 1
    · funext x
      rfl
    · simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := c) (b := 1) (fun t _ => hd t)
    ((by fun_prop : Continuous fun t : ℝ => t / c * Real.exp (-(m * t ^ 2))).intervalIntegrable _ _)
  have hb : (∫ h in c..1, Real.exp (-(m * h ^ 2))) ≤
      ∫ h in c..1, h / c * Real.exp (-(m * h ^ 2)) := by
    apply intervalIntegral.integral_mono_on hc1
    · exact (by fun_prop : Continuous fun h : ℝ => Real.exp (-(m * h ^ 2))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun h : ℝ => h / c * Real.exp (-(m * h ^ 2))).intervalIntegrable _ _
    · intro t ht
      have htc : 1 ≤ t / c := (le_div_iff₀ hc).mpr (by linarith [ht.1])
      nlinarith [Real.exp_pos (-(m * t ^ 2))]
  rw [hi] at hb
  have hpos : 0 ≤ Real.exp (-(m * (1 : ℝ) ^ 2)) / (2 * m * c) := by positivity
  simp only [neg_div, sub_neg_eq_add] at hb
  linarith

theorem norm_fm_ge_induction {m : ℕ} (hm : 2 ≤ m) :
    1 / √(2 * (m : ℝ)) ≤ 2 ^ (2 * m) * (m.factorial : ℝ) ^ 2 / (2 * m + 1).factorial := by
  induction' hm with k hk ih
  · have h_left : 1 / √(2 * ((2 : ℕ) : ℝ)) = 1 / 2 := by norm_num
    have h_right : 2 ^ (2 * 2) * (Nat.factorial 2 : ℝ) ^ 2 / Nat.factorial (2 * 2 + 1) = 8 / 15 := by norm_num
    rw [h_left, h_right]
    norm_num
  · have hk_pos : (0 : ℝ) < k := by
      have : 2 ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have h_left : 1 / √(2 * ((k + 1 : ℕ) : ℝ)) = 1 / √(2 * (k : ℝ) + 2) := by
      congr 2
      push_cast
      ring
    have h_right_eq : 2 ^ (2 * (k + 1)) * (Nat.factorial (k + 1) : ℝ) ^ 2 / Nat.factorial (2 * (k + 1) + 1) =
        (2 ^ (2 * k) * (Nat.factorial k : ℝ) ^ 2 / Nat.factorial (2 * k + 1)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)) := by
      have h1 : (2 : ℝ) ^ (2 * (k + 1)) = 2 ^ (2 * k) * (4 : ℝ) := by
        have : 2 * (k + 1) = 2 * k + 2 := by ring
        rw [this, pow_add]
        norm_num
      have h2 : (Nat.factorial (k + 1) : ℝ) ^ 2 = (Nat.factorial k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 := by
        have : (Nat.factorial (k + 1) : ℝ) = Nat.factorial k * ((k : ℝ) + 1) := by
          have hf : (k + 1).factorial = (k + 1) * k.factorial := rfl
          rw [hf]
          push_cast
          ring
        rw [this, mul_pow]
      have h3 : (Nat.factorial (2 * (k + 1) + 1) : ℝ) = (Nat.factorial (2 * k + 1) : ℝ) * ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3)) := by
        have h_eq : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
        rw [h_eq]
        have hf1 : (2 * k + 3).factorial = (2 * k + 3) * (2 * k + 2).factorial := rfl
        have hf2 : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1).factorial := rfl
        rw [hf1, hf2]
        push_cast
        ring
      rw [h1, h2, h3]
      have heq : (4 : ℝ) * ((k : ℝ) + 1) ^ 2 / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3)) = 2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3) := by
        have h_den : 2 * (k : ℝ) + 2 = 2 * ((k : ℝ) + 1) := by ring
        rw [h_den]
        have h_k_ne : (2 : ℝ) * ((k : ℝ) + 1) ≠ 0 := by positivity
        have : (4 : ℝ) * ((k : ℝ) + 1) ^ 2 = (2 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1)) := by ring
        rw [this, mul_div_mul_left _ _ h_k_ne]
      have h_k_ne2 : (Nat.factorial (2 * k + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      have h_k_ne3 : ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3)) ≠ 0 := by positivity
      calc ((2:ℝ) ^ (2 * k) * 4 * (Nat.factorial k ^ 2 * ((k : ℝ) + 1) ^ 2)) / (Nat.factorial (2 * k + 1) * ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3)))
        _ = ((2:ℝ) ^ (2 * k) * Nat.factorial k ^ 2 * (4 * ((k : ℝ) + 1) ^ 2)) / (Nat.factorial (2 * k + 1) * ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3))) := by ring
        _ = ((2:ℝ) ^ (2 * k) * Nat.factorial k ^ 2 / Nat.factorial (2 * k + 1)) * ((4 * ((k : ℝ) + 1) ^ 2) / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3))) := by
          rw [div_mul_div_comm]
        _ = ((2:ℝ) ^ (2 * k) * Nat.factorial k ^ 2 / Nat.factorial (2 * k + 1)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)) := by rw [heq]
    have h_le : 1 / √(2 * (k : ℝ) + 2) ≤ (2 ^ (2 * k) * (Nat.factorial k : ℝ) ^ 2 / Nat.factorial (2 * k + 1)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)) := by
      have h_ih_mul : 1 / √(2 * (k : ℝ)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)) ≤ (2 ^ (2 * k) * (Nat.factorial k : ℝ) ^ 2 / Nat.factorial (2 * k + 1)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)) := by
        have h_pos : 0 ≤ 2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3) := by positivity
        exact mul_le_mul_of_nonneg_right ih h_pos
      have h_bound : 1 / √(2 * (k : ℝ) + 2) ≤ 1 / √(2 * (k : ℝ)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)) := by
        have h_pos_sqrt : 0 < √(2 * (k : ℝ)) := by positivity
        have h_pos_sqrt2 : 0 < √(2 * (k : ℝ) + 2) := by positivity
        have h_pos_d : 0 < 2 * (k : ℝ) + 3 := by positivity
        have ht : (1 / √(2 * (k : ℝ) + 2) ≤ 1 / √(2 * (k : ℝ)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3))) ↔
                   (√(2 * (k : ℝ)) * (2 * (k : ℝ) + 3) ≤ √(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1))) := by
          have he : 1 / √(2 * (k : ℝ)) * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)) = (2 * ((k : ℝ) + 1)) / (√(2 * (k : ℝ)) * (2 * (k : ℝ) + 3)) := by
            rw [div_mul_div_comm, one_mul]
          rw [he]
          rw [div_le_div_iff₀ h_pos_sqrt2]
          · have hr : (√(2 * ↑k) * (2 * ↑k + 3) ≤ 2 * (↑k + 1) * √(2 * ↑k + 2)) ↔ (√(2 * ↑k) * (2 * ↑k + 3) ≤ √(2 * ↑k + 2) * (2 * (↑k + 1))) := by
              have h_rw : 2 * (↑k + 1) * √(2 * ↑k + 2) = √(2 * ↑k + 2) * (2 * (↑k + 1)) := by ring
              rw [h_rw]
            rw [one_mul]
            exact hr
          · positivity
        rw [ht]
        have hsq : (√(2 * (k : ℝ)) * (2 * (k : ℝ) + 3)) ^ 2 ≤ (√(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1))) ^ 2 := by
          have h1 : (√(2 * (k : ℝ)) * (2 * (k : ℝ) + 3)) ^ 2 = (2 * (k : ℝ)) * (2 * (k : ℝ) + 3) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          have h2 : (√(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1))) ^ 2 = (2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          rw [h1, h2]
          have h_diff : (2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1)) ^ 2 - (2 * (k : ℝ)) * (2 * (k : ℝ) + 3) ^ 2 = 6 * (k : ℝ) + 8 := by ring
          linarith
        have hp1 : 0 ≤ √(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1)) := by positivity
        have hsq2 : √(2 * (k : ℝ)) * (2 * (k : ℝ) + 3) * (√(2 * (k : ℝ)) * (2 * (k : ℝ) + 3)) ≤ √(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1)) * (√(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1))) := by
          have h_rw1 : (√(2 * (k : ℝ)) * (2 * (k : ℝ) + 3)) ^ 2 = √(2 * (k : ℝ)) * (2 * (k : ℝ) + 3) * (√(2 * (k : ℝ)) * (2 * (k : ℝ) + 3)) := by ring
          have h_rw2 : (√(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1))) ^ 2 = √(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1)) * (√(2 * (k : ℝ) + 2) * (2 * ((k : ℝ) + 1))) := by ring
          rw [← h_rw1, ← h_rw2]
          exact hsq
        exact nonneg_le_nonneg_of_sq_le_sq hp1 hsq2
      exact le_trans h_bound h_ih_mul
    rw [h_left, h_right_eq]
    exact h_le

/-- LEAF. Unit U-1531. For `m >= 2`, `||f_m||_1 >= (2m)^(-1/2)`; p. 23, line after (24). The
bound fails at `m = 1`, where `||f_1||_1 = 2/3 < 1/√2`. -/
theorem norm_fm_ge {m : ℕ} (hm : 2 ≤ m) : 1 / √(2 * m) ≤ ∫ t in (0 : ℝ)..1, fm m t := by
  have hsq : ∀ n : ℕ, 1 ≤ 2 * (n + 2 : ℝ) * (∫ t in (0 : ℝ)..1, fm (n + 2) t) ^ 2 := by
    intro n
    induction n with
    | zero => rw [norm_fm]; norm_num
    | succ n ih =>
      have hr := norm_fm_succ (n + 2)
      have hd : (0 : ℝ) < 2 * (n + 2) + 3 := by positivity
      have he : (∫ t in (0 : ℝ)..1, fm (n + 1 + 2) t) =
          (2 * (n + 2) + 2 : ℝ) / (2 * (n + 2) + 3) *
            (∫ t in (0 : ℝ)..1, fm (n + 2) t) := by
        rw [show n + 1 + 2 = n + 2 + 1 by omega]
        rw [div_mul_eq_mul_div, eq_div_iff hd.ne']
        push_cast at hr ⊢
        nlinarith [hr]
      have hratio : 2 * ((n + 2 : ℝ) + 1) *
          ((2 * (n + 2) + 2) / (2 * (n + 2) + 3)) ^ 2 ≥ 2 * (n + 2) := by
        change 2 * (n + 2 : ℝ) ≤ _
        rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hd 2)]
        nlinarith [show (0 : ℝ) ≤ n by positivity]
      have hb := mul_le_mul_of_nonneg_right hratio
        (sq_nonneg (∫ t in (0 : ℝ)..1, fm (n + 2) t))
      rw [he]
      push_cast
      nlinarith [hb]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1, fm (n + 2) t := by rw [norm_fm]; positivity
  have hs : 0 < √(2 * ((n + 2 : ℕ) : ℝ)) := by positivity
  have hss := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) by positivity)
  have hb := hsq n
  push_cast at hb hss hs ⊢
  rw [div_le_iff₀ hs]
  have hp : 0 ≤ (∫ t in (0 : ℝ)..1, fm (n + 2) t) * √(2 * (n + 2 : ℝ)) := by positivity
  have hh : 1 ≤ ((∫ t in (0 : ℝ)..1, fm (n + 2) t) * √(2 * (n + 2 : ℝ))) ^ 2 := by
    nlinarith [hb, hss]
  nlinarith

/-- LEAF. Unit U-1531. `e^(-4)/2 <= 1/16`, the choice `b = 1` on p. 23. -/
theorem exp_neg_four_half : Real.exp (-4) / 2 ≤ 1 / 16 := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
  rw [Real.exp_neg]
  have he : 0 < Real.exp 4 := Real.exp_pos _
  have hi : (Real.exp 4)⁻¹ ≤ (8 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith)
  norm_num at hi ⊢
  linarith

/-- LEAF. Unit U-1531. `mu*_2(f_2) = 40 √3 / 3`; p. 24, the short calculation after (28). -/
theorem muStar_two : muStar 2 = 40 * √3 / 3 := by
  let g : ℝ → ℝ := fun t => 32 - 192 * t + 192 * t ^ 2
  let G : ℝ → ℝ := fun t => 64 * t ^ 3 - 96 * t ^ 2 + 32 * t
  let r : ℝ := (3 - √3) / 6
  have hs3 : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hslo : (1 : ℝ) < √3 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hshi : √(3 : ℝ) < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hrhalf : r ≤ 1 - r := by dsimp [r]; linarith
  have hr1 : 1 - r ≤ 1 := by linarith
  have hrc : r * (1 - r) = 1 / 6 := by dsimp [r]; nlinarith
  have hfact (t : ℝ) : g t = 192 * (t - r) * (t - (1 - r)) := by
    dsimp [g]
    nlinarith [hrc]
  have hgcont : Continuous g := by dsimp [g]; fun_prop
  have hder (t : ℝ) : HasDerivAt G (g t) t := by
    change HasDerivAt (fun t : ℝ => 64 * t ^ 3 - 96 * t ^ 2 + 32 * t)
      (32 - 192 * t + 192 * t ^ 2) t
    convert ((((hasDerivAt_id t).pow 3).const_mul 64).sub
      (((hasDerivAt_id t).pow 2).const_mul 96)).add ((hasDerivAt_id t).const_mul 32) using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp; ring
  have hFTC (a b : ℝ) : (∫ t in a..b, g t) = G b - G a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hgcont.intervalIntegrable _ _)
  have hp : (∫ t in (0 : ℝ)..r, |g t|) = ∫ t in (0 : ℝ)..r, g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr0] at ht
    apply abs_of_nonneg
    rw [hfact]
    exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith [ht.2]) (by linarith [ht.2])
  have hn : (∫ t in r..(1 - r), |g t|) = -(∫ t in r..(1 - r), g t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hrhalf] at ht
    apply abs_of_nonpos
    rw [hfact]
    exact mul_nonpos_of_nonneg_of_nonpos (by nlinarith [ht.1]) (by linarith [ht.2])
  have hp' : (∫ t in (1 - r)..1, |g t|) = ∫ t in (1 - r)..1, g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr1] at ht
    apply abs_of_nonneg
    rw [hfact]
    exact mul_nonneg (by nlinarith [ht.1]) (by linarith [ht.1])
  have hc : √(3 : ℝ) ^ 3 = 3 * √3 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (sq_nonneg (√(3 : ℝ))),
      congrArg (fun x : ℝ => x * √3) hs3]
  have hGr : G r = 16 * √3 / 9 := by dsimp [G, r]; nlinarith [hs3, hc]
  have hGr' : G (1 - r) = -16 * √3 / 9 := by dsimp [G, r]; nlinarith [hs3, hc]
  have htotal : (∫ t in (0 : ℝ)..1, |g t|) = 64 * √3 / 9 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hgcont.abs.intervalIntegrable 0 (1 - r)) (hgcont.abs.intervalIntegrable (1 - r) 1),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hgcont.abs.intervalIntegrable 0 r) (hgcont.abs.intervalIntegrable r (1 - r)), hp, hn, hp']
    rw [hFTC, hFTC, hFTC, hGr, hGr']
    norm_num [G]
    ring
  have heq : iteratedDeriv 2 (fm 2) = g := by
    rw [LeanLab.RamareSaouter2003.MuStarUpper.iteratedDeriv_fm]
    funext t
    norm_num [LeanLab.RamareSaouter2003.MuStarUpper.F, Function.iterate_succ_apply',
      Polynomial.derivative_mul, Polynomial.derivative_pow, g]
    ring
  unfold muStar
  rw [heq, htotal, norm_fm]
  norm_num
  ring

/-- LEAF. Unit U-1531. With `m = 2`, `alpha1 = 0.63`, `alpha4 = 1/2`, `a = 2/25` and
`alpha2 >= 17.26`, which holds for `alpha2 = 0.5 log Y` and `Y >= 10^15`, the number `alpha3`
lies in `[6.189, 6.226]`; p. 24, first line of the list. -/
theorem alpha3_bounds {α2 : ℝ} (hα2 : 17.26 ≤ α2) :
    6.189 ≤ 1 / alpha3inv 2 0.63 α2 (1 / 2) (2 / 25) ∧
      1 / alpha3inv 2 0.63 α2 (1 / 2) (2 / 25) ≤ 6.226 := by
  set D := alpha3inv 2 0.63 α2 (1 / 2) (2 / 25)
  have he : D = (0.3233388125568 - 0.0326 / α2) / 2.0012 := by
    dsimp [D, alpha3inv, w]
    rw [w_f2]
    norm_num
  have hαpos : 0 < α2 := by linarith
  have hq0 : 0 ≤ 0.0326 / α2 := by positivity
  have hqhi : 0.0326 / α2 ≤ 0.0326 / 17.26 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hα2
  have hDpos : 0 < D := by
    rw [he]
    norm_num at hqhi ⊢
    linarith
  constructor
  · rw [le_div_iff₀ hDpos]
    rw [he]
    norm_num at hqhi ⊢
    linarith
  · rw [div_le_iff₀ hDpos]
    rw [he]
    norm_num
    linarith

/-- LEAF. Unit U-1531. For `Y >= 10^15`,
`-6.3 √Y/log Y + 0.58 + 0.67 log(√Y/log Y) <= 0`; p. 25, end of the bound for `h(Y)`. -/
theorem hY_nonpos {Y : ℝ} (hY : 10 ^ 15 ≤ Y) :
    -6.3 * √Y / Real.log Y + 0.58 + 0.67 * Real.log (√Y / Real.log Y) ≤ 0 := by
  have hY1 : 1 < Y := by linarith
  have hL : 0 < Real.log Y := Real.log_pos hY1
  have hq : 0 < √Y / Real.log Y := div_pos (Real.sqrt_pos.mpr (by linarith)) hL
  have hh := Real.log_le_sub_one_of_pos hq
  rw [show -6.3 * √Y / Real.log Y = -6.3 * (√Y / Real.log Y) by ring]
  nlinarith

/-- LEAF. Unit U-1531. For `Y >= 10^15` and `T = 2 alpha1 pi √Y/log Y` with `alpha1 = 0.63`,
`2 g(T/2pi) <= alpha1 √Y` where `g(x) = x log x - x + 7/8 + 0.67 log x`; p. 24, (29), and p. 25. -/
theorem twoG_le {Y : ℝ} (hY : 10 ^ 15 ≤ Y) :
    2 * ((2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi) *
          Real.log ((2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi)) -
        (2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi) + 7 / 8 +
        0.67 * Real.log ((2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi))) ≤
      0.63 * √Y := by
  have hY0 : 0 < Y := by linarith
  have hL1 : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < Real.log Y := by linarith
  have hsq : Real.log Y ≤ √Y := by
    have hh := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Real.log Y / 2 by positivity)
    rw [Real.exp_half, Real.exp_log hY0] at hh
    nlinarith [sq_nonneg (Real.log Y - 2)]
  let q := √Y / Real.log Y
  have hq1 : 1 ≤ q := (le_div_iff₀ hL0).mpr (by simpa [q] using hsq)
  have hq0 : 0 < q := by linarith
  have hqS : q ≤ √Y := by
    dsimp [q]
    exact div_le_self (Real.sqrt_nonneg _) hL1
  have hz : 0 < 0.63 * q := by positivity
  have hlog : Real.log (0.63 * q) ≤ Real.log Y / 2 := by
    rw [← Real.log_sqrt hY0.le]
    apply Real.log_le_log hz
    linarith
  have hmain : 0.63 * q * Real.log (0.63 * q) ≤ 0.315 * √Y := by
    calc
      0.63 * q * Real.log (0.63 * q) ≤ 0.63 * q * (Real.log Y / 2) :=
        mul_le_mul_of_nonneg_left hlog hz.le
      _ = 0.315 * √Y := by dsimp [q]; field_simp; ring
  have hsmall := Real.log_le_sub_one_of_pos hz
  have hident : (2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi) = 0.63 * q := by
    dsimp [q]
    field_simp
  rw [hident]
  nlinarith

/-- LEAF. Unit U-1531. For `Y >= 10^15` and `T = 2 alpha1 pi √Y/log Y` with `alpha1 = 0.63`,
`S2 = T s_2(T)/√Y` lies in `[0.25, 0.321]`; p. 24, third line of the list. -/
theorem S2_bounds {Y : ℝ} (hY : 10 ^ 15 ≤ Y) :
    0.25 ≤ (2 * 0.63 * Real.pi * √Y / Real.log Y) *
        sm 2 (2 * 0.63 * Real.pi * √Y / Real.log Y) / √Y ∧
      (2 * 0.63 * Real.pi * √Y / Real.log Y) *
        sm 2 (2 * 0.63 * Real.pi * √Y / Real.log Y) / √Y ≤ 0.321 := by
  have hY0 : 0 < Y := by linarith
  let L := Real.log Y
  let S := √Y
  have h10 : (2.3 : ℝ) ≤ Real.log 10 := by
    have he : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    rw [he]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hL : 34.5 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 15) hY
    rw [Real.log_pow] at hh
    norm_num at hh
    dsimp [L]
    nlinarith
  have hL0 : 0 < L := by linarith
  have hS0 : 0 < S := Real.sqrt_pos.mpr hY0
  have hlogL : Real.log L ≤ 0.103 * L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L / 32 by positivity)
    have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
    rw [Real.log_div hL0.ne' (by norm_num), h32] at hh
    nlinarith [Real.log_two_lt_d9]
  have hlogL1 : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    linarith [Real.exp_one_lt_d9]
  have hlogc : -0.5 ≤ Real.log (0.63 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.26 by norm_num)
    have he : Real.log (0.63 : ℝ) = Real.log 1.26 - Real.log 2 := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    rw [he]
    norm_num at hh
    linarith [Real.log_two_lt_d9]
  have hlogc0 : Real.log (0.63 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  let z := 0.63 * S / L
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hlogz : Real.log z = L / 2 - Real.log L + Real.log 0.63 := by
    dsimp [z]
    rw [Real.log_div (by positivity) hL0.ne', Real.log_mul (by norm_num) hS0.ne',
      Real.log_sqrt hY0.le]
    dsimp [L]
    ring
  have hzlo : 0 ≤ Real.log z := by rw [hlogz]; linarith
  have hzhi : Real.log z + 0.5 ≤ L / 2 := by rw [hlogz]; linarith
  have hzlow : 0.397 * L ≤ Real.log z + 0.5 := by rw [hlogz]; linarith
  have hmainlo : 0.25011 ≤ 0.63 / L * (Real.log z + 0.5) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
    nlinarith
  have hmainhi : 0.63 / L * (Real.log z + 0.5) ≤ 0.315 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL0]
    nlinarith
  have hSbig : 300 * (L + 1) ≤ S := by
    have hh := Real.pow_div_factorial_le_exp (L / 2) (by positivity) 5
    rw [Real.exp_half, Real.exp_log hY0] at hh
    change (L / 2) ^ 5 / (Nat.factorial 5 : ℝ) ≤ S at hh
    norm_num at hh
    have h4 : (34.5 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
    have h5 := mul_le_mul_of_nonneg_right h4 hL0.le
    nlinarith
  have hcorrlo : 0 ≤ 1.34 / S * (2 * Real.log z + 1) := by positivity
  have hcorrhi : 1.34 / S * (2 * Real.log z + 1) ≤ 1.34 / 300 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hS0]
    nlinarith
  have hid : (2 * 0.63 * Real.pi * S / L) / (2 * Real.pi) = z := by
    dsimp [z]
    field_simp
  have he : (2 * 0.63 * Real.pi * S / L) * sm 2 (2 * 0.63 * Real.pi * S / L) / S =
      (0.63 / L * (Real.log z + 0.5) + 1.34 / S * (2 * Real.log z + 1)) * 1.00001 := by
    unfold sm
    rw [hid]
    norm_num only [Nat.cast_ofNat, Nat.reducePow]
    field_simp [hL0.ne', hS0.ne', Real.pi_ne_zero]
    ring
  change 0.25 ≤ (2 * 0.63 * Real.pi * S / L) * sm 2 (2 * 0.63 * Real.pi * S / L) / S ∧
    (2 * 0.63 * Real.pi * S / L) * sm 2 (2 * 0.63 * Real.pi * S / L) / S ≤ 0.321
  rw [he]
  constructor <;> nlinarith

/-- LEAF. Unit U-1531. For `Z >= 0`, `theta(√Z) + theta(Z^(1/3)) <= psi(Z) - theta(Z)`, the
prime square and prime cube terms of `psi`; the first step toward the lower bound in (11),
p. 19. -/
theorem theta_sqrt_add_cbrt_le {Z : ℝ} (hZ : 0 ≤ Z) :
    θ (√Z) + θ (Z ^ ((1 : ℝ) / 3)) ≤ ψ Z - θ Z := by
  let N := ⌊Real.log Z / Real.log 2⌋₊ + 3
  have hpsi := Chebyshev.psi_eq_sum_theta' hZ (N := N) (by dsimp [N]; omega)
  have hsub : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 N := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hi ⊢
    dsimp [N]
    rcases hi with rfl | rfl | rfl <;> omega
  have hsum : (∑ i ∈ ({1, 2, 3} : Finset ℕ), θ (Z ^ (1 / (i : ℝ)))) ≤
      ∑ i ∈ Finset.Icc 1 N, θ (Z ^ (1 / (i : ℝ))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    exact Chebyshev.theta_nonneg _
  norm_num at hsum
  rw [← Real.sqrt_eq_rpow] at hsum
  simp only [one_div] at hpsi
  rw [← hpsi] at hsum
  linarith

/-- LEAF. Unit U-1531. Stirling form of (21): for `m >= 1`,
`(2m + 1)!/(m! √(2m + 1)) <= √(4m + 2) e^(1/(24m)) (4m/e)^m`; p. 21, (21) with (24). -/
theorem muM_stirling {m : ℕ} (hm : 1 ≤ m) :
    ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * √(2 * m + 1)) ≤
      √(4 * m + 2) * Real.exp (1 / (24 * m)) * (4 * m / Real.exp 1) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hM : (0 : ℝ) < m.factorial := by positivity
  have hS : 0 < √(2 * (m : ℝ) + 1) := by positivity
  have hupper := Stirling126.factorial_upper (n := 2 * m) (by omega)
  have hlower := Stirling.le_factorial_stirling m
  push_cast at hupper hlower
  let A : ℝ := √(2 * Real.pi * m) * (m / Real.exp 1) ^ m
  let B : ℝ := √(2 * Real.pi * (2 * m)) * ((2 * m) / Real.exp 1) ^ (2 * m) *
    Real.exp (1 / (24 * m))
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : ((2 * m).factorial : ℝ) ≤ B := by
    convert hupper using 1 <;> dsimp [B]
    congr 1
    congr 1
    ring
  have hAlower : A ≤ (m.factorial : ℝ) := hlower
  have hfac : ((2 * m + 1).factorial : ℝ) / ((m.factorial : ℝ) * √(2 * m + 1)) =
      √(2 * m + 1) * ((2 * m).factorial : ℝ) / m.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    calc
      (2 * (m : ℝ) + 1) * ((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * √(2 * m + 1)) =
          √(2 * m + 1) ^ 2 * ((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * √(2 * m + 1)) := by
            rw [Real.sq_sqrt (by positivity)]
      _ = _ := by field_simp
  have hsqrt : √(2 * Real.pi * (2 * (m : ℝ))) = √2 * √(2 * Real.pi * m) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    ring
  have hpow : ((2 * (m : ℝ)) / Real.exp 1) ^ (2 * m) =
      (4 * m / Real.exp 1) ^ m * (m / Real.exp 1) ^ m := by
    rw [pow_mul, ← mul_pow]
    congr 1
    ring
  have hBfactor : B = √2 * (4 * m / Real.exp 1) ^ m * Real.exp (1 / (24 * m)) * A := by
    dsimp [A, B]
    rw [hsqrt, hpow]
    ring
  have hC : √(4 * (m : ℝ) + 2) = √(2 * m + 1) * √2 := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [hfac]
  calc
    √(2 * (m : ℝ) + 1) * ((2 * m).factorial : ℝ) / m.factorial ≤
        √(2 * m + 1) * B / m.factorial :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _)) hM.le
    _ ≤ √(2 * m + 1) * B / A :=
      div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) hB) hA hAlower
    _ = √(4 * m + 2) * Real.exp (1 / (24 * m)) * (4 * m / Real.exp 1) ^ m := by
      rw [hBfactor, hC]
      field_simp

/-! ### Assemblies -/

/-- **(25) to (27), p. 23.** For `a` in `[0, 1/2]`, `v(f_m, a)` is at most the integral of
`e^(-m h^2)` over `[1 - 2a, 1]`. PROVED CONDITIONAL ON `v_fm_eq` and
`one_sub_sq_pow_le_exp`. -/
theorem v_le_gauss (m : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    v (fm m) a ≤ ∫ h in (1 - 2 * a)..1, Real.exp (-(m * h ^ 2)) := by
  rw [v_fm_eq m ha0 ha1]
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (by fun_prop : Continuous fun h : ℝ => (1 - h ^ 2) ^ m).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun h : ℝ => Real.exp (-(m * h ^ 2))).intervalIntegrable _ _
  · intro h hh
    exact one_sub_sq_pow_le_exp m (by linarith [hh.1]) hh.2

/-- **The bound on `w(f_m, a)` of p. 23.** For `m >= 2`, `b > 0` and `b <= √m/2`, with
`a = 1/2 - b/√m`, `w(f_m, a) <= e^(-4b^2)/(2b)`. PROVED CONDITIONAL ON `v_fm_eq`,
`one_sub_sq_pow_le_exp`, `gauss_tail` and `norm_fm_ge`. -/
theorem w_fm_le {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (hb : 0 < b) (hbm : b ≤ √m / 2) :
    w m (1 / 2 - b / √m) ≤ Real.exp (-4 * b ^ 2) / (2 * b) := by
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hs : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hss : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm0.le
  have ha0 : 0 ≤ 1 / 2 - b / √m := by
    rw [sub_nonneg, div_le_iff₀ hs]; linarith
  have ha1 : 1 / 2 - b / √m ≤ 1 / 2 := by
    have : 0 ≤ b / √m := by positivity
    linarith
  have hc : 1 - 2 * (1 / 2 - b / √m) = 2 * b / √m := by ring
  have hc0 : 0 < 2 * b / √m := by positivity
  have hc1 : 2 * b / √m ≤ 1 := by rw [div_le_iff₀ hs]; linarith
  have hv := v_le_gauss m ha0 ha1
  rw [hc] at hv
  have ht := gauss_tail hm0 hc0 hc1
  have hexp : (m : ℝ) * (2 * b / √m) ^ 2 = 4 * b ^ 2 := by
    rw [div_pow, Real.sq_sqrt hm0.le]; field_simp <;> ring
  have hden : 2 * (m : ℝ) * (2 * b / √m) = 4 * b * √m := by
    nth_rewrite 1 [← hss]; field_simp <;> ring
  rw [hexp, hden] at ht
  have hV : v (fm m) (1 / 2 - b / √m) ≤ Real.exp (-(4 * b ^ 2)) / (4 * b * √m) := hv.trans ht
  have hF := norm_fm_ge hm
  have h2m : √(2 * (m : ℝ)) = √2 * √m := Real.sqrt_mul (by norm_num) _
  rw [h2m] at hF
  have h2 : 0 < √(2 : ℝ) := by positivity
  have h22 : √(2 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hFpos : 0 < ∫ t in (0 : ℝ)..1, fm m t := lt_of_lt_of_le (by positivity) hF
  have hE : 0 < Real.exp (-(4 * b ^ 2)) := Real.exp_pos _
  unfold w
  rw [div_le_iff₀ hFpos]
  have hneg : Real.exp (-4 * b ^ 2) = Real.exp (-(4 * b ^ 2)) := by ring_nf
  rw [hneg]
  have hq : 1 / (2 * √(m : ℝ)) ≤ ∫ t in (0 : ℝ)..1, fm m t := by
    refine le_trans ?_ hF
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right h22 hs.le)
  calc v (fm m) (1 / 2 - b / √m) ≤ Real.exp (-(4 * b ^ 2)) / (4 * b * √m) := hV
    _ = Real.exp (-(4 * b ^ 2)) / (2 * b) * (1 / (2 * √m)) := by
        field_simp; ring
    _ ≤ Real.exp (-(4 * b ^ 2)) / (2 * b) * (∫ t in (0 : ℝ)..1, fm m t) :=
        mul_le_mul_of_nonneg_left hq (by positivity)

/-- **The case `b = 1` on p. 23.** For `m >= 4`, `w(f_m, 1/2 - 1/√m) <= 1/16`. PROVED
CONDITIONAL ON the leaves of `w_fm_le` and `exp_neg_four_half`. -/
theorem w_fm_le_sixteenth {m : ℕ} (hm : 4 ≤ m) : w m (1 / 2 - 1 / √m) ≤ 1 / 16 := by
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : (2 : ℝ) ≤ √m := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have h := w_fm_le (m := m) (by omega) one_pos (by linarith)
  have h4 : Real.exp (-4 * 1 ^ 2) / (2 * 1) = Real.exp (-4) / 2 := by norm_num
  rw [h4] at h
  exact h.trans exp_neg_four_half

/-- **Last inequality of the list on p. 24.** For `u >= 0` and `a = 2/25`,
`(1 + 2(1 - a)u - (1 + 2au)e^(-u))/(1 + 2(1 - a)u) <= 2.68 u`. PROVED from `lemma7` of
`Theorem3Smooth`. -/
theorem section6_interval {u : ℝ} (hu : 0 ≤ u) :
    (1 + 2 * (1 - 2 / 25) * u - (1 + 2 * (2 / 25) * u) * Real.exp (-u)) /
        (1 + 2 * (1 - 2 / 25) * u) ≤ 2.68 * u := by
  have h := lemma7 (m := 2) (u := u) (a := 2 / 25) (by norm_num) hu (by norm_num) (by norm_num)
  have hD : 0 < 1 + 2 * (1 - 2 / 25 : ℝ) * u := by nlinarith
  have heq : (1 + 2 * (1 - 2 / 25) * u - (1 + 2 * (2 / 25) * u) * Real.exp (-u)) /
        (1 + 2 * (1 - 2 / 25) * u) =
      1 - (1 + 2 * u * (2 / 25)) / (1 + 2 * u * (1 - 2 / 25)) * Real.exp (-u) := by
    field_simp <;> ring
  rw [heq]
  calc _ ≤ u * (1 + (1 - 2 * (2 / 25)) * 2) := h
    _ = 2.68 * u := by ring

/-- **The hypothesis `2N(T) <= alpha1 √Y` of Section 6, p. 24.** If `N(T)` satisfies the upper
bound of Lemma 1 at `T = 2 alpha1 pi √Y/log Y` with `alpha1 = 0.63`, and `Y >= 10^15`, then
`2N(T) <= 0.63 √Y`. PROVED CONDITIONAL ON `twoG_le`. -/
theorem twoN_le_section6 {Y NT : ℝ} (hY : 10 ^ 15 ≤ Y)
    (hN : NT ≤ (2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi) *
          Real.log ((2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi)) -
        (2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi) + 7 / 8 +
        0.67 * Real.log ((2 * 0.63 * Real.pi * √Y / Real.log Y) / (2 * Real.pi))) :
    2 * NT ≤ 0.63 * √Y := by
  have := twoG_le hY
  linarith

end LeanLab.RamareSaouter2003.Decomp1531c
