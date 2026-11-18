import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Selberg majorant, the two cotangent inequalities at non-nodes

AI wrote this Lean code. Binary Goldbach is OPEN; this file is analytic infrastructure only.
`cot` is written `cos / sin` on purpose.
-/

namespace LeanLab.ExceptionalSet.Selberg524

open Real Finset

private lemma cot_sub524 (a b : ℝ) (ha : sin a ≠ 0) (hb : sin b ≠ 0) :
    cos a / sin a - cos b / sin b = sin (b - a) / (sin a * sin b) := by
  rw [sin_sub]
  field_simp

private lemma tele524 (a d : ℝ) (m : ℕ) (h : ∀ i ≤ m, sin (a - (i : ℝ) * d) ≠ 0) :
    cos a / sin a - cos (a - (m : ℝ) * d) / sin (a - (m : ℝ) * d) =
      -sin d * ∑ i ∈ range m, 1 / (sin (a - (i : ℝ) * d) * sin (a - ((i + 1 : ℕ) : ℝ) * d)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (fun i hi => h i (by omega))
    have key := cot_sub524 (a - (m : ℝ) * d) (a - ((m + 1 : ℕ) : ℝ) * d)
      (h m (by omega)) (h (m + 1) le_rfl)
    have e : a - ((m + 1 : ℕ) : ℝ) * d - (a - (m : ℝ) * d) = -d := by push_cast; ring
    rw [e, sin_neg] at key
    rw [sum_range_succ, mul_add, ← ih']
    linear_combination key

private lemma sum_abs_mul_le524 (q : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, |q i * q (i + 1)| + q n ^ 2 / 2 ≤ ∑ i ∈ range (n + 1), q i ^ 2 := by
  induction n with
  | zero => simp; nlinarith [sq_nonneg (q 0)]
  | succ n ih =>
    rw [sum_range_succ _ (n + 1), sum_range_succ _ n]
    have h : |q n * q (n + 1)| ≤ (q n ^ 2 + q (n + 1) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|q n| - |q (n + 1)|), sq_abs (q n), sq_abs (q (n + 1))]
    linarith

theorem selberg_nonneg524 (N : ℝ) (hN : 1 ≤ N) (k : ℕ) (θ : ℝ)
    (hs : ∀ i ∈ range (2 * k + 1), sin (π * (θ - ((i : ℝ) - (k : ℝ)) / N)) ≠ 0) :
    0 ≤ (1 / N ^ 2) * ∑ i ∈ range (2 * k + 1), 1 / sin (π * (θ - ((i : ℝ) - (k : ℝ)) / N)) ^ 2 +
      (1 / (π * N)) * (cos (π * (θ + (k : ℝ) / N)) / sin (π * (θ + (k : ℝ) / N)) -
        cos (π * (θ - (k : ℝ) / N)) / sin (π * (θ - (k : ℝ) / N))) := by
  have hN0 : 0 < N := by linarith
  have hdpos : 0 ≤ π / N := by positivity
  have hd0 : 0 ≤ sin (π / N) :=
    sin_nonneg_of_nonneg_of_le_pi hdpos (div_le_self pi_pos.le hN)
  have hd1 : sin (π / N) ≤ π / N := sin_le hdpos
  have e1 : ∀ i : ℕ, π * (θ - ((i : ℝ) - (k : ℝ)) / N) = π * (θ + (k : ℝ) / N) - (i : ℝ) * (π / N) := by
    intro i; ring
  have e2 : π * (θ - (k : ℝ) / N) = π * (θ + (k : ℝ) / N) - ((2 * k : ℕ) : ℝ) * (π / N) := by
    push_cast; ring
  simp only [e1] at hs ⊢
  rw [e2]
  generalize π * (θ + (k : ℝ) / N) = a at *
  have ht := tele524 a (π / N) (2 * k) (fun i hi => hs i (mem_range.2 (by omega)))
  have hq := sum_abs_mul_le524 (fun i : ℕ => 1 / sin (a - (i : ℝ) * (π / N))) (2 * k)
  simp only [one_div_pow] at hq
  rw [ht]
  have hPS : ∑ i ∈ range (2 * k), 1 / (sin (a - (i : ℝ) * (π / N)) *
      sin (a - ((i + 1 : ℕ) : ℝ) * (π / N))) ≤
      ∑ i ∈ range (2 * k + 1), 1 / sin (a - (i : ℝ) * (π / N)) ^ 2 := by
    have h1 : ∑ i ∈ range (2 * k), 1 / (sin (a - (i : ℝ) * (π / N)) *
        sin (a - ((i + 1 : ℕ) : ℝ) * (π / N))) ≤
        ∑ i ∈ range (2 * k), |1 / sin (a - (i : ℝ) * (π / N)) *
          (1 / sin (a - ((i + 1 : ℕ) : ℝ) * (π / N)))| := by
      apply sum_le_sum
      intro i _
      rw [one_div_mul_one_div]
      exact le_abs_self _
    have h2 : 0 ≤ 1 / sin (a - ((2 * k : ℕ) : ℝ) * (π / N)) ^ 2 / 2 := by positivity
    linarith
  have hS0 : 0 ≤ ∑ i ∈ range (2 * k + 1), 1 / sin (a - (i : ℝ) * (π / N)) ^ 2 :=
    sum_nonneg (fun i _ => by positivity)
  generalize (∑ i ∈ range (2 * k), 1 / (sin (a - (i : ℝ) * (π / N)) *
      sin (a - ((i + 1 : ℕ) : ℝ) * (π / N)))) = P at *
  generalize (∑ i ∈ range (2 * k + 1), 1 / sin (a - (i : ℝ) * (π / N)) ^ 2) = S at *
  have h3 : sin (π / N) * P ≤ π / N * S :=
    (mul_le_mul_of_nonneg_left hPS hd0).trans (mul_le_mul_of_nonneg_right hd1 hS0)
  have h4 : 1 / (π * N) * (sin (π / N) * P) ≤ 1 / (π * N) * (π / N * S) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : 1 / (π * N) * (π / N * S) = 1 / N ^ 2 * S := by
    have := pi_pos.ne'
    field_simp
  have h6 : 1 / (π * N) * (-sin (π / N) * P) = -(1 / (π * N) * (sin (π / N) * P)) := by ring
  rw [h6]
  linarith

private lemma alg524 (d sd cd sb cb : ℝ) (hd : 0 ≤ d) (hcd : 0 ≤ cd) (h : d * cd ≤ sd)
    (e1 : sd ^ 2 + cd ^ 2 = 1) (e2 : sb ^ 2 + cb ^ 2 = 1) :
    2 * d * (sb ^ 2 - sd ^ 2) ≤ 2 * sd * cd * sb ^ 2 := by
  have A := mul_nonneg (mul_nonneg hcd (sq_nonneg sb)) (sub_nonneg.2 h)
  have B := mul_nonneg (mul_nonneg hd (sq_nonneg sd)) (sq_nonneg cb)
  have hc : cd ^ 2 = 1 - sd ^ 2 := by linarith
  have hb : cb ^ 2 = 1 - sb ^ 2 := by linarith
  rw [hb] at B
  have A' : 0 ≤ cd * sb ^ 2 * sd - d * sb ^ 2 * (1 - sd ^ 2) := by
    rw [← hc]; linarith
  linarith

private lemma pt524 (b d : ℝ) (hd : 0 < d) (hd2 : d < π / 2) (h1 : 0 < b - d) (h2 : b + d < π) :
    1 / sin b ^ 2 ≤
      1 / (2 * d) * (cos (b - d) / sin (b - d) - cos (b + d) / sin (b + d)) := by
  have hp := sin_pos_of_pos_of_lt_pi h1 (by linarith)
  have hq := sin_pos_of_pos_of_lt_pi (by linarith : 0 < b + d) h2
  have hb := sin_pos_of_pos_of_lt_pi (by linarith : 0 < b) (by linarith)
  have hcd : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith, hd2⟩
  have htan := (Real.lt_tan hd hd2).le
  have hdc : d * cos d ≤ sin d := by
    rw [tan_eq_sin_div_cos, le_div_iff₀ hcd] at htan; exact htan
  have hprod : sin (b - d) * sin (b + d) = sin b ^ 2 - sin d ^ 2 := by
    rw [sin_sub, sin_add]
    linear_combination (sin b) ^ 2 * sin_sq_add_cos_sq d - (sin d) ^ 2 * sin_sq_add_cos_sq b
  have halg := alg524 d (sin d) (cos d) (sin b) (cos b) hd.le hcd.le hdc
    (sin_sq_add_cos_sq d) (sin_sq_add_cos_sq b)
  have hpos : 0 < sin b ^ 2 - sin d ^ 2 := by rw [← hprod]; exact mul_pos hp hq
  rw [cot_sub524 _ _ hp.ne' hq.ne', show b + d - (b - d) = 2 * d by ring, sin_two_mul, hprod,
    div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

private lemma cotdec524 (x d : ℝ) (hx : 0 < x) (hd : 0 < d) (h : x + d < π) :
    cos (x + d) / sin (x + d) ≤ cos x / sin x := by
  have hp := sin_pos_of_pos_of_lt_pi hx (by linarith)
  have hq := sin_pos_of_pos_of_lt_pi (by linarith : 0 < x + d) h
  have hsd := sin_pos_of_pos_of_lt_pi hd (by linarith)
  have key := cot_sub524 x (x + d) hp.ne' hq.ne'
  rw [show x + d - x = d by ring] at key
  have : 0 < sin d / (sin x * sin (x + d)) := by positivity
  linarith

private lemma tele2_524 (c : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range m, (c j - c (j + 2)) = c 0 + c 1 - c m - c (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; ring

private lemma sumB524 (w d : ℝ) (m : ℕ) (hw : 0 < w) (hd : 0 < d) (hd2 : d < π / 2)
    (hn : w + ((m : ℝ) + 1) * d < π) :
    ∑ j ∈ range m, 1 / sin (w + ((j : ℝ) + 1) * d) ^ 2 ≤
      1 / d * (cos w / sin w - cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d)) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmd : 0 ≤ (m : ℝ) * d := by positivity
  have htele := tele2_524 (fun j : ℕ => cos (w + (j : ℝ) * d) / sin (w + (j : ℝ) * d)) m
  have h0 : w + ((0 : ℕ) : ℝ) * d = w := by simp
  have h1 : w + ((1 : ℕ) : ℝ) * d = w + d := by simp
  have hm1 : w + ((m + 1 : ℕ) : ℝ) * d = w + ((m : ℝ) + 1) * d := by push_cast; ring
  simp only [h0, h1, hm1] at htele
  have hpt : ∀ j ∈ range m, 1 / sin (w + ((j : ℝ) + 1) * d) ^ 2 ≤
      1 / (2 * d) * (cos (w + (j : ℝ) * d) / sin (w + (j : ℝ) * d) -
        cos (w + ((j + 2 : ℕ) : ℝ) * d) / sin (w + ((j + 2 : ℕ) : ℝ) * d)) := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt (mem_range.1 hj)
    have hjd : 0 ≤ (j : ℝ) * d := by positivity
    have hjmd : ((j : ℝ) + 1) * d ≤ (m : ℝ) * d := mul_le_mul_of_nonneg_right hjm hd.le
    have ea : w + ((j : ℝ) + 1) * d - d = w + (j : ℝ) * d := by ring
    have eb : w + ((j : ℝ) + 1) * d + d = w + ((j + 2 : ℕ) : ℝ) * d := by push_cast; ring
    have := pt524 (w + ((j : ℝ) + 1) * d) d hd hd2 (by rw [ea]; linarith)
      (by nlinarith)
    rw [ea, eb] at this
    exact this
  have hc1 : cos (w + d) / sin (w + d) ≤ cos w / sin w :=
    cotdec524 w d hw hd (by nlinarith)
  have hcm : cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d) ≤
      cos (w + (m : ℝ) * d) / sin (w + (m : ℝ) * d) := by
    have := cotdec524 (w + (m : ℝ) * d) d (by linarith) hd (by linarith)
    rw [show w + (m : ℝ) * d + d = w + ((m : ℝ) + 1) * d by ring] at this
    exact this
  calc ∑ j ∈ range m, 1 / sin (w + ((j : ℝ) + 1) * d) ^ 2
      ≤ ∑ j ∈ range m, 1 / (2 * d) * (cos (w + (j : ℝ) * d) / sin (w + (j : ℝ) * d) -
        cos (w + ((j + 2 : ℕ) : ℝ) * d) / sin (w + ((j + 2 : ℕ) : ℝ) * d)) := sum_le_sum hpt
    _ = 1 / (2 * d) * (cos w / sin w + cos (w + d) / sin (w + d) -
          cos (w + (m : ℝ) * d) / sin (w + (m : ℝ) * d) -
          cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d)) := by
        rw [← mul_sum, htele]
    _ ≤ 1 / (2 * d) * (2 * (cos w / sin w -
          cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 1 / d * (cos w / sin w -
          cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d)) := by
        rw [← mul_assoc]
        congr 1
        field_simp

theorem selberg_ge_one524 (M k : ℕ) (hk : 2 * k + 2 ≤ M) (θ : ℝ)
    (h1 : -((k : ℝ) / (M : ℝ)) < θ) (h2 : θ < (k : ℝ) / (M : ℝ)) :
    (1 / (M : ℝ) ^ 2) * ∑ i ∈ Ico (2 * k + 1) M, 1 / sin (π * (θ - ((i : ℝ) - (k : ℝ)) / (M : ℝ))) ^ 2 ≤
      (1 / (π * (M : ℝ))) * (cos (π * (θ + (k : ℝ) / (M : ℝ))) / sin (π * (θ + (k : ℝ) / (M : ℝ))) -
        cos (π * (θ - (k : ℝ) / (M : ℝ))) / sin (π * (θ - (k : ℝ) / (M : ℝ)))) := by
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    simp at h1 h2
    linarith
  have hM4 : (4 : ℝ) ≤ M := by exact_mod_cast (by omega : 4 ≤ M)
  have hM : (0 : ℝ) < M := by linarith
  have hpi := pi_pos
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = π / M := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = π * ((k : ℝ) / M - θ) := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = M - (2 * k + 1) := ⟨_, rfl⟩
  have hmr : (m : ℝ) = (M : ℝ) - 2 * k - 1 := by
    rw [hm_def, Nat.cast_sub (by omega)]; push_cast; ring
  have hd : 0 < d := by rw [hd_def]; positivity
  have hd2 : d < π / 2 := by
    rw [hd_def, div_lt_div_iff₀ hM two_pos]; nlinarith
  have hw : 0 < w := by rw [hw_def]; exact mul_pos hpi (by linarith)
  have hy : w + ((m : ℝ) + 1) * d = π - π * (θ + (k : ℝ) / M) := by
    rw [hw_def, hd_def, hmr]; field_simp; ring
  have hn : w + ((m : ℝ) + 1) * d < π := by
    rw [hy]
    have := mul_pos hpi (by linarith : 0 < θ + (k : ℝ) / M)
    linarith
  have B := sumB524 w d m hw hd hd2 hn
  have hL : ∑ i ∈ Ico (2 * k + 1) M, 1 / sin (π * (θ - ((i : ℝ) - (k : ℝ)) / (M : ℝ))) ^ 2 =
      ∑ j ∈ range m, 1 / sin (w + ((j : ℝ) + 1) * d) ^ 2 := by
    rw [sum_Ico_eq_sum_range, ← hm_def]
    apply sum_congr rfl
    intro j _
    have : π * (θ - (((2 * k + 1 + j : ℕ) : ℝ) - (k : ℝ)) / (M : ℝ)) =
        -(w + ((j : ℝ) + 1) * d) := by
      rw [hw_def, hd_def]; push_cast; field_simp; ring
    rw [this, sin_neg, neg_sq]
  have hR : cos (π * (θ + (k : ℝ) / (M : ℝ))) / sin (π * (θ + (k : ℝ) / (M : ℝ))) -
        cos (π * (θ - (k : ℝ) / (M : ℝ))) / sin (π * (θ - (k : ℝ) / (M : ℝ))) =
      cos w / sin w - cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d) := by
    have ea : π * (θ + (k : ℝ) / (M : ℝ)) = π - (w + ((m : ℝ) + 1) * d) := by rw [hy]; ring
    have eb : π * (θ - (k : ℝ) / (M : ℝ)) = -w := by rw [hw_def]; ring
    rw [ea, eb, cos_pi_sub, sin_pi_sub, cos_neg, sin_neg, neg_div, div_neg]
    ring
  rw [hL, hR]
  calc 1 / (M : ℝ) ^ 2 * ∑ j ∈ range m, 1 / sin (w + ((j : ℝ) + 1) * d) ^ 2
      ≤ 1 / (M : ℝ) ^ 2 * (1 / d * (cos w / sin w -
          cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d))) :=
        mul_le_mul_of_nonneg_left B (by positivity)
    _ = 1 / (π * (M : ℝ)) * (cos w / sin w -
          cos (w + ((m : ℝ) + 1) * d) / sin (w + ((m : ℝ) + 1) * d)) := by
        rw [← mul_assoc]
        congr 1
        rw [hd_def]
        field_simp

end LeanLab.ExceptionalSet.Selberg524
