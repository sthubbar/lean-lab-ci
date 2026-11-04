import LeanLab.LZCesaroShort.Lemma13Statements
import LeanLab.LZCesaroShort.Lemma3Parseval
import LeanLab.LZCesaroShort.Lemma3Reduction
import LeanLab.LZCesaroShort.Lemma3Comparison

namespace LeanLab.LZCesaroShort

open Complex MeasureTheory Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt

namespace J209

/-! ### Elementary exponential and geometric estimates -/

private lemma exp_neg_le_one_sub_add_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hsum : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 3
    simpa [Finset.sum_range_succ, Nat.factorial] using h
  have hA : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have hle : 1 / (1 + x + x ^ 2 / 2) ≤ 1 - x + x ^ 2 / 2 := by
    rw [div_le_iff₀ hA]
    have hEq : (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) = 1 + (x ^ 2 / 2) ^ 2 := by ring
    nlinarith [sq_nonneg (x ^ 2 / 2)]
  calc Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + x + x ^ 2 / 2) := one_div_le_one_div_of_le hA hsum
    _ ≤ 1 - x + x ^ 2 / 2 := hle

private lemma one_sub_le_exp_neg {x : ℝ} (hx : 0 ≤ x) : 1 - x ≤ Real.exp (-x) := by
  have := Real.add_one_le_exp (-x)
  linarith

private lemma one_sub_exp_neg_ge {x : ℝ} (hx : 0 ≤ x) :
    x * (1 - x / 2) ≤ 1 - Real.exp (-x) := by
  have h := exp_neg_le_one_sub_add_sq hx
  nlinarith [h]

private lemma inv_one_sub_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    1 / (1 - u) ≤ 1 + 2 * u := by
  have hpos : 0 < 1 - u := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [sq_nonneg u, mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - 2 * u)]

private lemma summable_nat_exp {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-2 * n / N)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := Real.summable_pow_mul_exp_neg_nat_mul 1 (show (0 : ℝ) < 2 / (N : ℝ) by positivity)
  refine h.congr (fun n => ?_)
  simp only [pow_one]
  congr 1
  ring

private lemma summable_log_exp {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => Real.log (n : ℝ) * Real.exp (-2 * n / N)) := by
  refine Summable.of_norm_bounded (summable_nat_exp hN) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn
    have hl : Real.log (n : ℝ) ≤ (n : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) by linarith)
      linarith
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_of_nonneg hl0]
    exact mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le

/-- The geometric sum is at least `N/2`. -/
private lemma geo_sum_lower {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) / 2 ≤ ∑' n : ℕ, Real.exp (-2 * n / N) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set x : ℝ := 2 / (N : ℝ) with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_iff₀ hN0]
    linarith
  have hle : 1 - Real.exp (-x) ≤ x := by
    have h := one_sub_le_exp_neg (le_of_lt hx0)
    linarith
  have hA := tsum_exp_two_eq hN1
  have hq : Real.exp (-2 / (N : ℝ)) = Real.exp (-x) := by rw [hxdef]; congr 1; ring
  rw [hA, hq]
  have h1q : 0 < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hkey := one_div_le_one_div_of_le h1q hle
  have hxe : 1 / x = (N : ℝ) / 2 := by
    rw [hxdef]; field_simp
  linarith [hkey, hxe]

/-- The geometric sum is at most `N/2 + 1`. -/
private lemma geo_sum_upper {N : ℕ} (hN : 2 ≤ N) :
    (∑' n : ℕ, Real.exp (-2 * n / N)) ≤ (N : ℝ) / 2 + 1 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set x : ℝ := 2 / (N : ℝ) with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_iff₀ hN0]
    linarith
  have hx2 : x / 2 ≤ 1 / 2 := by linarith
  have hlow : x * (1 - x / 2) ≤ 1 - Real.exp (-x) := one_sub_exp_neg_ge (le_of_lt hx0)
  have hpos : 0 < x * (1 - x / 2) := by nlinarith
  have hA := tsum_exp_two_eq hN1
  have hq : Real.exp (-2 / (N : ℝ)) = Real.exp (-x) := by rw [hxdef]; congr 1; ring
  rw [hA, hq]
  have hkey : 1 / (1 - Real.exp (-x)) ≤ 1 / (x * (1 - x / 2)) :=
    one_div_le_one_div_of_le hpos hlow
  have hsplit : 1 / (x * (1 - x / 2)) = (1 / x) * (1 / (1 - x / 2)) := by field_simp
  have hxe : 1 / x = (N : ℝ) / 2 := by rw [hxdef]; field_simp
  have hb : 1 / (1 - x / 2) ≤ 1 + x := by
    have := inv_one_sub_le (by linarith : (0:ℝ) ≤ x / 2) hx2
    linarith
  have hNx : (N : ℝ) * x = 2 := by rw [hxdef]; field_simp
  have hfin : (1 / x) * (1 / (1 - x / 2)) ≤ ((N : ℝ) / 2) * (1 + x) := by
    apply mul_le_mul hxe.le hb
    · exact div_nonneg zero_le_one (by linarith)
    · positivity
  rw [hsplit] at hkey
  nlinarith [hkey, hfin, hNx]

/-! ### Comparing `∑ log n` with `∫ log t` -/

/-- `N log N - N ≤ ∑_{n<N} log (n+1)`, the monotone comparison for `log`. -/
private lemma sum_log_ge_log {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ ∑ n ∈ Finset.range N, Real.log ((n + 1 : ℕ) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hmono : MonotoneOn Real.log (Set.Icc (1 : ℝ) (1 + ((N - 1 : ℕ) : ℝ))) := by
    intro s hs t ht hst
    rw [Set.mem_Icc] at hs ht
    exact Real.log_le_log (by linarith [hs.1]) hst
  have hint := MonotoneOn.integral_le_sum (x₀ := (1 : ℝ)) (a := N - 1) (f := Real.log) hmono
  have hlim : (1 : ℝ) + ((N - 1 : ℕ) : ℝ) = (N : ℝ) := by
    have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub hN]; norm_num
    linarith
  have hval : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
    rw [integral_log]
    simp
  have het : ∑ i ∈ Finset.range (N - 1), Real.log (1 + ((i + 1 : ℕ) : ℝ))
      = ∑ n ∈ Finset.range N, Real.log ((n + 1 : ℕ) : ℝ) := by
    have hN' : N = (N - 1) + 1 := (Nat.sub_add_cancel hN).symm
    rw [hN', Finset.sum_range_succ']
    norm_num
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring_nf
  rw [hlim, hval] at hint
  rw [← het]
  linarith [hint]

/-- `∑_{n ≤ N} log (N/n) ≤ N`. -/
private lemma sum_log_div_N_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ)) ≤ (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hid : ∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ))
      = (N : ℝ) * Real.log (N : ℝ) - ∑ n ∈ Finset.range N, Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, Real.log_zero, add_zero]
    have hp : ∀ k ∈ Finset.range N,
        Real.log ((N : ℝ) / ((k + 1 : ℕ) : ℝ)) = Real.log (N : ℝ) - Real.log ((k + 1 : ℕ) : ℝ) := by
      intro k hk
      have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [Real.log_div (ne_of_gt hN0) hk1]
    rw [Finset.sum_congr rfl hp, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  rw [hid]
  linarith [sum_log_ge_log hN]

/-! ### The weighted sums -/

private lemma exp_two_div_eq_pow (N n : ℕ) :
    Real.exp (-2 * (n : ℝ) / (N : ℝ)) = Real.exp (-(2 / (N : ℝ))) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma sum_nat_mul_geo_le {N : ℕ} (hN : 2 ≤ N) :
    (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * n / N)) ≤ (N : ℝ) ^ 2 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set q : ℝ := Real.exp (-(2 / (N : ℝ))) with hqdef
  have hq1 : q < 1 := by
    rw [hqdef, Real.exp_lt_one_iff]
    simp only [neg_lt_zero]
    positivity
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have heq : ∀ n : ℕ, (n : ℝ) * Real.exp (-2 * n / N) = (n : ℝ) * q ^ n := by
    intro n
    rw [exp_two_div_eq_pow N n, hqdef]
  have hqs : Real.exp (-2 / (N : ℝ)) = q := by rw [hqdef]; congr 1; ring
  rw [tsum_congr heq, tsum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])]
  have hA := geo_sum_upper hN
  rw [tsum_exp_two_eq hN1, hqs] at hA
  have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1q : 0 < 1 - q := by linarith
  have hAN : 1 / (1 - q) ≤ (N : ℝ) := by linarith
  have hsq : (1 / (1 - q)) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hAN 2
  have hrew : q / (1 - q) ^ 2 = q * (1 / (1 - q)) ^ 2 := by
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [hrew]
  calc q * (1 / (1 - q)) ^ 2 ≤ 1 * (1 / (1 - q)) ^ 2 := by
        apply mul_le_mul_of_nonneg_right (le_of_lt hq1) (sq_nonneg _)
    _ = (1 / (1 - q)) ^ 2 := one_mul _
    _ ≤ (N : ℝ) ^ 2 := hsq

/-- The weighted head `∑_{n ≤ N} log (N/n) e^{-2n/N} ≤ N`. -/
private lemma sum_head_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ)) * Real.exp (-2 * n / N) ≤ (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hstep : ∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ)) * Real.exp (-2 * n / N)
      ≤ ∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_range] at hn
    have hnN : n ≤ N := by omega
    have hlog0 : 0 ≤ Real.log ((N : ℝ) / (n : ℝ)) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · apply Real.log_nonneg
        rw [le_div_iff₀ (by exact_mod_cast h : (0 : ℝ) < (n : ℝ))]
        have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
        linarith
    have he1 : Real.exp (-2 * n / N) ≤ 1 := by
      have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) / (N : ℝ) := by positivity
      have harg : -2 * (n : ℝ) / (N : ℝ) = -(2 * (n : ℝ) / (N : ℝ)) := by ring
      rw [harg]
      calc Real.exp (-(2 * (n : ℝ) / (N : ℝ))) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    calc Real.log ((N : ℝ) / (n : ℝ)) * Real.exp (-2 * n / N)
        ≤ Real.log ((N : ℝ) / (n : ℝ)) * 1 := mul_le_mul_of_nonneg_left he1 hlog0
      _ = Real.log ((N : ℝ) / (n : ℝ)) := mul_one _
  linarith [hstep, sum_log_div_N_le hN]

/-- The weighted tail `∑_{n > N} log (n/N) e^{-2n/N} ≤ N`. -/
private lemma sum_tail_le {N : ℕ} (hN : 2 ≤ N) :
    ∑' k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
        * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N) ≤ (N : ℝ) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set g : ℕ → ℝ := fun k => ((k + (N + 1) : ℕ) : ℝ) * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N) with hg
  have hgs : Summable g := by
    have h := summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) * Real.exp (-2 * n / N)) (N + 1)
    rw [hg]
    exact h.mpr (summable_nat_exp hN1)
  have hterm : ∀ k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
        * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N) ≤ (1 / (N : ℝ)) * g k := by
    intro k
    have hmN : N ≤ k + (N + 1) := by omega
    have hmpos : 0 < (((k + (N + 1) : ℕ)) : ℝ) := by
      exact_mod_cast (show 0 < k + (N + 1) by omega)
    have h1 : Real.log ((((k + (N + 1) : ℕ)) : ℝ) / (N : ℝ))
        ≤ ((((k + (N + 1) : ℕ)) : ℝ) / (N : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : ((((k + (N + 1) : ℕ)) : ℝ) / (N : ℝ)) - 1 ≤ (((k + (N + 1) : ℕ)) : ℝ) / (N : ℝ) := by
      linarith
    have he : 0 ≤ Real.exp (-2 * (((k + (N + 1) : ℕ)) : ℝ) / N) := (Real.exp_pos _).le
    calc Real.log ((((k + (N + 1) : ℕ)) : ℝ) / (N : ℝ)) * Real.exp (-2 * (((k + (N + 1) : ℕ)) : ℝ) / N)
        ≤ ((((k + (N + 1) : ℕ)) : ℝ) / (N : ℝ)) * Real.exp (-2 * (((k + (N + 1) : ℕ)) : ℝ) / N) :=
          mul_le_mul_of_nonneg_right (le_trans h1 h2) he
      _ = (1 / (N : ℝ)) * g k := by
          rw [hg]
          simp only
          field_simp
  have hnn : ∀ k : ℕ, 0 ≤ Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
      * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N) := by
    intro k
    apply mul_nonneg _ (Real.exp_pos _).le
    apply Real.log_nonneg
    rw [le_div_iff₀ hN0]
    have hmN : N ≤ k + (N + 1) := by omega
    have : (N : ℝ) ≤ (((k + (N + 1) : ℕ)) : ℝ) := by exact_mod_cast hmN
    linarith
  have hlhs : Summable (fun k : ℕ => Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
      * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N)) :=
    Summable.of_nonneg_of_le hnn hterm (hgs.mul_left _)
  have hmain := Summable.tsum_le_tsum hterm hlhs (hgs.mul_left (1 / (N : ℝ)))
  rw [tsum_mul_left] at hmain
  have hshift : ∑' k : ℕ, g k
      = (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * n / N))
        - ∑ n ∈ Finset.range (N + 1), (n : ℝ) * Real.exp (-2 * n / N) := by
    have h := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => (n : ℝ) * Real.exp (-2 * n / N))
      (N + 1) (summable_nat_exp hN1)
    rw [hg]
    simp only
    linarith [h]
  rw [hshift] at hmain
  have hhead_nn : 0 ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ) * Real.exp (-2 * n / N) :=
    Finset.sum_nonneg (fun n hn => by positivity)
  have hgeo := sum_nat_mul_geo_le hN
  calc ∑' k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
        * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N)
      ≤ (1 / (N : ℝ)) * ((∑' n : ℕ, (n : ℝ) * Real.exp (-2 * n / N))
          - ∑ n ∈ Finset.range (N + 1), (n : ℝ) * Real.exp (-2 * n / N)) := hmain
    _ ≤ (1 / (N : ℝ)) * ((N : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = (N : ℝ) := by field_simp


/-- `log (n/N) e^{-2n/N}` is summable. -/
private lemma summable_log_div_exp {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNn0 : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hmaj : Summable (fun n : ℕ => (Real.log (N : ℝ) + (n : ℝ)) * Real.exp (-2 * n / N)) := by
    have h1 : Summable (fun n : ℕ => Real.log (N : ℝ) * Real.exp (-2 * n / N)) :=
      (summable_exp_two hN).mul_left _
    have h2 : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-2 * n / N)) := summable_nat_exp hN
    refine (h1.add h2).congr (fun n => ?_)
    ring
  refine Summable.of_norm_bounded hmaj (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simpa using hlogN
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have he : 0 ≤ Real.exp (-2 * (n : ℝ) / (N : ℝ)) := (Real.exp_pos _).le
    have e1 : Real.log ((N : ℝ) / (n : ℝ)) = Real.log (N : ℝ) - Real.log (n : ℝ) :=
      Real.log_div hNn0 hn0
    have e2 : Real.log ((n : ℝ) / (N : ℝ)) = Real.log (n : ℝ) - Real.log (N : ℝ) :=
      Real.log_div hn0 hNn0
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    by_cases hnN : n ≤ N
    · have h1 : Real.log ((n : ℝ) / (N : ℝ)) ≤ 0 := by
        rw [e2]
        have h2 : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by linarith) (by exact_mod_cast hnN)
        linarith
      rw [abs_of_nonpos h1]
      have hneg : -Real.log ((n : ℝ) / (N : ℝ)) = Real.log ((N : ℝ) / (n : ℝ)) := by
        rw [e1, e2]; ring
      rw [hneg]
      have h2 : Real.log ((N : ℝ) / (n : ℝ)) ≤ Real.log (N : ℝ) := by
        rw [e1]
        have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
        linarith
      exact mul_le_mul_of_nonneg_right (by linarith : Real.log ((N : ℝ) / (n : ℝ)) ≤ Real.log (N : ℝ) + (n : ℝ)) he
    · have h1 : 0 ≤ Real.log ((n : ℝ) / (N : ℝ)) := by
        rw [e2]
        have h2 : Real.log (N : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by linarith) (by exact_mod_cast (le_of_not_ge hnN : N ≤ n))
        linarith
      rw [abs_of_nonneg h1]
      have h4 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n : ℝ) / (N : ℝ))
      have h6 : (n : ℝ) / (N : ℝ) - 1 ≤ (n : ℝ) := by
        have h7 : (n : ℝ) / (N : ℝ) - 1 ≤ (n : ℝ) / (N : ℝ) := by
          have hsub : (n : ℝ) / (N : ℝ) - 1 = ((n : ℝ) - (N : ℝ)) / (N : ℝ) := by field_simp
          rw [hsub]
          apply div_le_div_of_nonneg_right _ hN0.le
          linarith
        have h8 : (n : ℝ) / (N : ℝ) ≤ (n : ℝ) := by
          have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          exact div_le_self (by linarith) hN1r
        linarith
      exact mul_le_mul_of_nonneg_right (by linarith : Real.log ((n : ℝ) / (N : ℝ)) ≤ Real.log (N : ℝ) + (n : ℝ)) he

/-- `|∑ log (n/N) e^{-2n/N}| ≤ 2N`. -/
private lemma log_div_tsum_bound {N : ℕ} (hN : 2 ≤ N) :
    |∑' n : ℕ, Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N)| ≤ 2 * (N : ℝ) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNn0 : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hs : Summable (fun n : ℕ => Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N)) :=
    summable_log_div_exp hN1
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N)) (N + 1) hs
  have hhead : ∑ n ∈ Finset.range (N + 1), Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N)
      = -∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ)) * Real.exp (-2 * n / N) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn0 : (n : ℝ) ≠ 0 := by positivity
      rw [Real.log_div hn0 hNn0, Real.log_div hNn0 hn0]
      ring
  have hheadnn : 0 ≤ ∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ)) * Real.exp (-2 * n / N) := by
    apply Finset.sum_nonneg
    intro n hn
    rw [Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · apply mul_nonneg _ (Real.exp_pos _).le
      apply Real.log_nonneg
      rw [le_div_iff₀ (by exact_mod_cast h : (0 : ℝ) < (n : ℝ))]
      have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : n ≤ N)
      linarith
  have htailnn : 0 ≤ ∑' k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
      * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N) := by
    apply tsum_nonneg
    intro k
    apply mul_nonneg _ (Real.exp_pos _).le
    apply Real.log_nonneg
    rw [le_div_iff₀ hN0]
    have hmN : N ≤ k + (N + 1) := by omega
    have : (N : ℝ) ≤ (((k + (N + 1) : ℕ)) : ℝ) := by exact_mod_cast hmN
    linarith
  have habs : (∑' n : ℕ, Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N))
      = (∑ n ∈ Finset.range (N + 1), Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N))
        + ∑' k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
            * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N) := by
    linarith [hsplit]
  rw [habs]
  calc |(∑ n ∈ Finset.range (N + 1), Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N))
        + ∑' k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
            * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N)|
      ≤ |∑ n ∈ Finset.range (N + 1), Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N)|
        + |∑' k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
            * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N)| := abs_add_le _ _
    _ = (∑ n ∈ Finset.range (N + 1), Real.log ((N : ℝ) / (n : ℝ)) * Real.exp (-2 * n / N))
        + ∑' k : ℕ, Real.log (((k + (N + 1) : ℕ) : ℝ) / (N : ℝ))
            * Real.exp (-2 * ((k + (N + 1) : ℕ)) / N) := by
        rw [hhead, abs_neg, abs_of_nonneg hheadnn, abs_of_nonneg htailnn]
    _ ≤ (N : ℝ) + (N : ℝ) := add_le_add (sum_head_le hN1) (sum_tail_le hN)
    _ = 2 * (N : ℝ) := by ring

/-- `∑ log n e^{-2n/N} = (N/2) log N + O(N)`. -/
private lemma log_tsum_asymptotic : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N)) - (N : ℝ) / 2 * Real.log (N : ℝ)|
      ≤ K * (N : ℝ) := by
  refine ⟨5, 10, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (by norm_num) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNn0 : (N : ℝ) ≠ 0 := ne_of_gt hN0
  set F : ℕ → ℝ := fun n => Real.log (n : ℝ) * Real.exp (-2 * n / N) with hF
  set G : ℕ → ℝ := fun n => Real.exp (-2 * n / N) with hG
  set B : ℕ → ℝ := fun n => Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N) with hB
  have hFs : Summable F := summable_log_exp hN1
  have hGs : Summable G := summable_exp_two hN1
  have hBs : Summable B := summable_log_div_exp hN1
  have hzero : ∑' n : ℕ, (Real.log (n : ℝ) - Real.log (N : ℝ) - Real.log ((n : ℝ) / (N : ℝ)))
      * Real.exp (-2 * n / N) = -Real.log (N : ℝ) := by
    have hbracket : ∀ n : ℕ, (Real.log (n : ℝ) - Real.log (N : ℝ) - Real.log ((n : ℝ) / (N : ℝ)))
        * Real.exp (-2 * n / N) = if n = 0 then -Real.log (N : ℝ) else 0 := by
      intro n
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hne : n ≠ 0 := by omega
        rw [Real.log_div hn0 hNn0]
        simp only [hne, if_false]
        ring
    rw [tsum_congr hbracket]
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp
  have hkey : (∑' n : ℕ, F n) - Real.log (N : ℝ) * (∑' n : ℕ, G n) - (∑' n : ℕ, B n)
      = -Real.log (N : ℝ) := by
    rw [← hzero, ← tsum_mul_left (f := G) (a := Real.log (N : ℝ))]
    rw [← Summable.tsum_sub hFs (hGs.mul_left (Real.log (N : ℝ)))]
    rw [← Summable.tsum_sub (hFs.sub (hGs.mul_left (Real.log (N : ℝ)))) hBs]
    exact tsum_congr (fun n => by rw [hF, hG, hB]; ring)
  have hkey' : (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N))
      - Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N))
      - (∑' n : ℕ, Real.log ((n : ℝ) / (N : ℝ)) * Real.exp (-2 * n / N)) = -Real.log (N : ℝ) := by
    simpa only [hF, hG, hB] using hkey
  have hL : (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N))
      = Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N))
        + (∑' n : ℕ, B n) - Real.log (N : ℝ) := by
    linarith [hkey']
  rw [hL]
  have hA1 := geo_sum_lower hN2
  have hA2 := geo_sum_upper hN2
  have hBb := log_div_tsum_bound hN2
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hlogN_le : Real.log (N : ℝ) ≤ (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos hN0
    linarith
  have hAabs : |(∑' n : ℕ, Real.exp (-2 * n / N)) - (N : ℝ) / 2| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hlogabs : |Real.log (N : ℝ)| = Real.log (N : ℝ) := abs_of_nonneg hlogN0
  have h1 : |Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N)) - Real.log (N : ℝ) * ((N : ℝ) / 2)|
      ≤ Real.log (N : ℝ) * 1 := by
    rw [← mul_sub, abs_mul, hlogabs]
    exact mul_le_mul_of_nonneg_left hAabs hlogN0
  have hmain : |Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N)) + (∑' n : ℕ, B n) - Real.log (N : ℝ)
      - (N : ℝ) / 2 * Real.log (N : ℝ)|
      ≤ |Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N)) - Real.log (N : ℝ) * ((N : ℝ) / 2)|
        + |∑' n : ℕ, B n| + |Real.log (N : ℝ)| := by
    have heq : Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N)) + (∑' n : ℕ, B n)
        - Real.log (N : ℝ) - (N : ℝ) / 2 * Real.log (N : ℝ)
        = (Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N)) - Real.log (N : ℝ) * ((N : ℝ) / 2))
          + (∑' n : ℕ, B n) - Real.log (N : ℝ) := by ring
    rw [heq]
    have h3 := abs_add_le (Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N)) - Real.log (N : ℝ) * ((N : ℝ) / 2))
      (∑' n : ℕ, B n)
    have h4 := abs_sub ((Real.log (N : ℝ) * (∑' n : ℕ, Real.exp (-2 * n / N)) - Real.log (N : ℝ) * ((N : ℝ) / 2))
      + (∑' n : ℕ, B n)) (Real.log (N : ℝ))
    linarith [h3, h4]
  linarith [hmain, h1, hBb, hlogN_le, hlogN0, hlogabs]


/-! ### The prime number theorem input -/

/-- de la Vallée Poussin form of the prime number theorem, from the ported `StrongPNT`. -/
private lemma psi_explicit_strong :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hO⟩ := StrongPNT
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hC
  set X := max x0 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  set m := 2 * Real.exp (-c * Real.sqrt (Real.log X)) with hm
  have hmpos : 0 < m := by positivity
  refine ⟨c, hc, max C ((Chebyshev.psi X + X) / m), fun x hx => ?_⟩
  have hxpos : 0 < x := by linarith
  have hE : 0 < x * Real.exp (-c * Real.sqrt (Real.log x)) := by positivity
  rcases le_total X x with hXx | hxX
  · have h := hx0 x (le_trans (le_max_left _ _) hXx)
    simp only [Pi.sub_apply, id, Real.norm_eq_abs] at h
    rw [← Real.sqrt_eq_rpow, abs_of_pos hE] at h
    calc |Chebyshev.psi x - x| ≤ C * (x * Real.exp (-c * Real.sqrt (Real.log x))) := h
      _ ≤ max C ((Chebyshev.psi X + X) / m) * (x * Real.exp (-c * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
      _ = max C ((Chebyshev.psi X + X) / m) * x
            * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
  · have h1 : |Chebyshev.psi x - x| ≤ Chebyshev.psi X + X := by
      have h2 := Chebyshev.psi_nonneg x
      have h3 := Chebyshev.psi_mono hxX
      rw [abs_le]; constructor <;> linarith
    have h2 : m ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hl : Real.log x ≤ Real.log X := Real.log_le_log hxpos hxX
      have hs : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hl
      have he : Real.exp (-c * Real.sqrt (Real.log X)) ≤ Real.exp (-c * Real.sqrt (Real.log x)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      exact mul_le_mul hx he (by positivity) (by linarith)
    have h0 : 0 ≤ Chebyshev.psi X + X := by
      have := Chebyshev.psi_nonneg X; linarith
    have hK : Chebyshev.psi X + X ≤
        (Chebyshev.psi X + X) / m * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
      exact mul_le_mul_of_nonneg_left h2 h0
    calc |Chebyshev.psi x - x| ≤ Chebyshev.psi X + X := h1
      _ ≤ (Chebyshev.psi X + X) / m * (x * Real.exp (-c * Real.sqrt (Real.log x))) := hK
      _ ≤ max C ((Chebyshev.psi X + X) / m) * (x * Real.exp (-c * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le
      _ = max C ((Chebyshev.psi X + X) / m) * x
            * Real.exp (-c * Real.sqrt (Real.log x)) := by ring

/-- The same bound at natural arguments, with a constant at least one. -/
private lemma psi_error_nat : ∃ K : ℝ, 1 ≤ K ∧ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    |Chebyshev.psi (n : ℝ) - (n : ℝ)|
      ≤ K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by
  obtain ⟨c, hc, K, hK⟩ := psi_explicit_strong
  refine ⟨max K 1, le_max_right _ _, c, hc, fun n hn => ?_⟩
  rcases Nat.eq_or_lt_of_le hn with h | h
  · have hpsi : Chebyshev.psi ((1 : ℕ) : ℝ) = 0 :=
      Chebyshev.psi_eq_zero_of_lt_two (by norm_num : ((1 : ℕ) : ℝ) < 2)
    have hn1 : n = 1 := h.symm
    subst hn1
    rw [hpsi]
    have hsimp : |(0 : ℝ) - ((1 : ℕ) : ℝ)| = 1 := by norm_num
    rw [hsimp]
    have he : Real.exp (-c * Real.sqrt (Real.log ((1 : ℕ) : ℝ))) = 1 := by simp
    rw [he]
    norm_num
  · have hx : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    calc |Chebyshev.psi (n : ℝ) - (n : ℝ)|
        ≤ K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := hK (n : ℝ) hx
      _ ≤ max K 1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by
          have hpos : 0 ≤ (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by positivity
          calc K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
              = K * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) := by ring
            _ ≤ max K 1 * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
            _ = max K 1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by ring

/-- The same for `θ`, with the extra `2 √n log n` from Mathlib's `|ψ - θ|` bound. -/
private lemma theta_error_nat : ∃ K : ℝ, 1 ≤ K ∧ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    |Chebyshev.theta (n : ℝ) - (n : ℝ)|
      ≤ K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
        + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨K, hK1, c, hc, hK⟩ := psi_error_nat
  refine ⟨K, hK1, c, hc, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpt := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hn1
  have hsplit : Chebyshev.theta (n : ℝ) - (n : ℝ)
      = -(Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) + (Chebyshev.psi (n : ℝ) - (n : ℝ)) := by
    ring
  rw [hsplit]
  calc |-(Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) + (Chebyshev.psi (n : ℝ) - (n : ℝ))|
      ≤ |Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)| + |Chebyshev.psi (n : ℝ) - (n : ℝ)| := by
        simpa only [abs_neg] using
          abs_add_le (-(Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) (Chebyshev.psi (n : ℝ) - (n : ℝ))
    _ ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
          + K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) :=
        add_le_add hpt (hK n hn)
    _ = K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
          + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by ring

/-- `log n · e^{-c√(log n)}` is bounded, uniformly in `n ≥ 1`. -/
private lemma log_mul_exp_neg_sqrt_bounded {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s * Real.exp (-c * Real.sqrt s) ≤ C := by
  refine ⟨2 / c ^ 2, by positivity, fun s hs => ?_⟩
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · rw [← hs0, Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one]
    positivity
  · set u := Real.sqrt s with hu
    have hu0 : 0 < u := Real.sqrt_pos.mpr hs0
    have hsq : u ^ 2 = s := by rw [hu]; exact Real.sq_sqrt hs
    have hcu0 : (0 : ℝ) ≤ c * u := by positivity
    have hexp : (c * u) ^ 2 / 2 ≤ Real.exp (c * u) := by
      have h := Real.sum_le_exp_of_nonneg hcu0 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
      nlinarith [h, hcu0]
    have hexppos : 0 < Real.exp (c * u) := Real.exp_pos _
    have hcu : 0 < (c * u) ^ 2 / 2 := by positivity
    have heq : Real.exp (-c * Real.sqrt s) = (Real.exp (c * u))⁻¹ := by
      rw [hu, ← Real.exp_neg]; ring_nf
    rw [← hsq, heq]
    have hle : u ^ 2 * (Real.exp (c * u))⁻¹ ≤ u ^ 2 / ((c * u) ^ 2 / 2) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hexppos hcu).mpr hexp) (by positivity)
    have hfin : u ^ 2 / ((c * u) ^ 2 / 2) = 2 / c ^ 2 := by
      field_simp
    linarith [hle, hfin]

/-- One step of the exponential weight. -/
private lemma exp_step (N n : ℕ) :
    Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
      = Real.exp (-2 * (n : ℝ) / (N : ℝ)) * Real.exp (-(2 / (N : ℝ))) := by
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

private lemma one_sub_exp_neg_two_le {N : ℕ} (hN : 2 ≤ N) :
    1 - Real.exp (-(2 / (N : ℝ))) ≤ 2 / (N : ℝ) := by
  have hx : 0 ≤ 2 / (N : ℝ) := by positivity
  have h := one_sub_le_exp_neg hx
  linarith

/-- The difference of the weight `log n e^{-2n/N}` is `O((1/n + N⁻¹ log n)) e^{-2n/N}`. -/
private lemma g_diff_bound {N : ℕ} (hN : 2 ≤ N) {n : ℕ} (hn : 1 ≤ n) :
    |Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))|
      ≤ (1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1))
        * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have he : 0 ≤ Real.exp (-2 * (n : ℝ) / (N : ℝ)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(2 / (N : ℝ))) ≤ 1 := by
    calc Real.exp (-(2 / (N : ℝ))) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by simp; positivity)
      _ = 1 := Real.exp_zero
  have hqe : |Real.exp (-(2 / (N : ℝ))) - 1| = 1 - Real.exp (-(2 / (N : ℝ))) := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hde : |Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
      - Real.exp (-2 * (n : ℝ) / (N : ℝ))|
      ≤ Real.exp (-2 * (n : ℝ) / (N : ℝ)) * (2 / (N : ℝ)) := by
    rw [exp_step]
    have hfac : Real.exp (-2 * (n : ℝ) / (N : ℝ)) * Real.exp (-(2 / (N : ℝ)))
        - Real.exp (-2 * (n : ℝ) / (N : ℝ))
        = Real.exp (-2 * (n : ℝ) / (N : ℝ)) * (Real.exp (-(2 / (N : ℝ))) - 1) := by ring
    rw [hfac, abs_mul, abs_of_nonneg he, hqe]
    exact mul_le_mul_of_nonneg_left (one_sub_exp_neg_two_le hN) he
  have hlogstep : Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    have hfac : ((n + 1 : ℕ) : ℝ) = (n : ℝ) * (1 + 1 / (n : ℝ)) := by
      push_cast; field_simp
    rw [hfac, Real.log_mul (ne_of_gt hn0) (by positivity)]
    have hpos1 : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos1
    field_simp at h ⊢
    linarith
  have hlogpos : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    push_cast
    linarith
  have hlogpos' : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlogstep0 : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) := by
    have h := Real.log_le_log hn0 (by push_cast; linarith : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    linarith
  have hdd : Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
      - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))
      = Real.log ((n + 1 : ℕ) : ℝ)
          * (Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ)) - Real.exp (-2 * (n : ℝ) / (N : ℝ)))
        + (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
          * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by ring
  rw [hdd]
  calc |Real.log ((n + 1 : ℕ) : ℝ)
        * (Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ)) - Real.exp (-2 * (n : ℝ) / (N : ℝ)))
      + (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
        * Real.exp (-2 * (n : ℝ) / (N : ℝ))|
      ≤ |Real.log ((n + 1 : ℕ) : ℝ)
        * (Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ)) - Real.exp (-2 * (n : ℝ) / (N : ℝ)))|
        + |(Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
        * Real.exp (-2 * (n : ℝ) / (N : ℝ))| := abs_add_le _ _
    _ ≤ Real.log ((n + 1 : ℕ) : ℝ) * (Real.exp (-2 * (n : ℝ) / (N : ℝ)) * (2 / (N : ℝ)))
        + (1 / (n : ℝ)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg hlogpos]
          exact mul_le_mul_of_nonneg_left hde hlogpos
        · rw [abs_mul, abs_of_nonneg he, abs_of_nonneg hlogstep0]
          exact mul_le_mul_of_nonneg_right hlogstep he
    _ ≤ (1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1))
        * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
        have hlog1 : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) + 1 := by
          have hle1 : 1 / (n : ℝ) ≤ 1 := by
            rw [div_le_one hn0]
            exact_mod_cast hn
          linarith
        have hstep' : Real.log ((n + 1 : ℕ) : ℝ)
            * (Real.exp (-2 * (n : ℝ) / (N : ℝ)) * (2 / (N : ℝ)))
            ≤ (Real.log (n : ℝ) + 1) * (Real.exp (-2 * (n : ℝ) / (N : ℝ)) * (2 / (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hlog1 (by positivity)
        calc Real.log ((n + 1 : ℕ) : ℝ) * (Real.exp (-2 * (n : ℝ) / (N : ℝ)) * (2 / (N : ℝ)))
              + (1 / (n : ℝ)) * Real.exp (-2 * (n : ℝ) / (N : ℝ))
            ≤ (Real.log (n : ℝ) + 1) * (Real.exp (-2 * (n : ℝ) / (N : ℝ)) * (2 / (N : ℝ)))
              + (1 / (n : ℝ)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by linarith [hstep']
          _ = (1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1))
              * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by ring


/-! ### Abel summation -/

private lemma sum_telescope (g : ℕ → ℝ) (hg0 : g 0 = 0) (K : ℕ) :
    ∑ n ∈ Finset.range K, (n : ℝ) * (g (n + 1) - g n)
      = (K : ℝ) * g K - ∑ n ∈ Finset.range (K + 1), g n := by
  induction K with
  | zero => simp [hg0]
  | succ K ih =>
      have hR : ∑ x ∈ Finset.range (K + 1 + 1), g x = ∑ x ∈ Finset.range (K + 1), g x + g (K + 1) := by
        rw [Finset.sum_range_succ]
      have hL : ∑ x ∈ Finset.range (K + 1), g x = ∑ x ∈ Finset.range K, g x + g K := by
        rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ, ih, hR, hL]
      push_cast
      ring

/-- Abel summation for a sequence `a` with cumulative sums `A`. -/
private lemma abel_identity (a g A : ℕ → ℝ) (hA : ∀ n, A n = ∑ i ∈ Finset.range (n + 1), a i)
    (hg0 : g 0 = 0) (K : ℕ) :
    ∑ n ∈ Finset.range (K + 1), a n * g n
      = (∑ n ∈ Finset.range (K + 1), g n) + (A K - (K : ℝ)) * g K
        - ∑ n ∈ Finset.range K, (A n - (n : ℝ)) * (g (n + 1) - g n) := by
  have h1 := Finset.sum_range_by_parts (f := g) (g := a) (K + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at h1
  have h2 : ∀ i : ℕ, (∑ j ∈ Finset.range (i + 1), a j) = A i := fun i => (hA i).symm
  simp only [h2] at h1
  have hS1 : ∑ n ∈ Finset.range (K + 1), a n * g n
      = A K * g K - ∑ i ∈ Finset.range K, A i * (g (i + 1) - g i) := by
    calc ∑ n ∈ Finset.range (K + 1), a n * g n
        = ∑ n ∈ Finset.range (K + 1), g n * a n := Finset.sum_congr rfl (fun i _ => by ring)
      _ = A K * g K - ∑ i ∈ Finset.range K, A i * (g (i + 1) - g i) := by
          rw [h1, mul_comm (g K) (A K)]
          exact congrArg (fun z => A K * g K - z)
            (Finset.sum_congr rfl (fun i _ => by ring))
  have hD : ∑ n ∈ Finset.range K, (A n - (n : ℝ)) * (g (n + 1) - g n)
      = ∑ i ∈ Finset.range K, A i * (g (i + 1) - g i)
        - ∑ i ∈ Finset.range K, (i : ℝ) * (g (i + 1) - g i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hS1, hD, sum_telescope g hg0 K]
  ring

/-- The Abel summation error bound. -/
private lemma abel_tsum_error {a A g : ℕ → ℝ} (hA : ∀ n, A n = ∑ i ∈ Finset.range (n + 1), a i)
    (hg0 : g 0 = 0) (has : Summable (fun n => a n * g n)) (hgs : Summable g)
    (hEs : Summable (fun n => (A n - (n : ℝ)) * (g (n + 1) - g n)))
    (hEabs : Summable (fun n => |(A n - (n : ℝ)) * (g (n + 1) - g n)|))
    (hC : Tendsto (fun K : ℕ => (A K - (K : ℝ)) * g K) atTop (𝓝 0)) :
    |(∑' n, a n * g n) - (∑' n, g n)|
      ≤ ∑' n, |(A n - (n : ℝ)) * (g (n + 1) - g n)| := by
  have h1 : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range (K + 1), a n * g n) atTop
      (𝓝 (∑' n, a n * g n)) := by
    have hs : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, a n * g n) atTop
        (𝓝 (∑' n, a n * g n)) := has.hasSum.tendsto_sum_nat
    have hz : Tendsto (fun K : ℕ => a K * g K) atTop (𝓝 0) := has.tendsto_atTop_zero
    have hh := hs.add hz
    simpa only [Finset.sum_range_succ, add_zero] using hh
  have h2 : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range (K + 1), g n) atTop (𝓝 (∑' n, g n)) := by
    have hs : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, g n) atTop (𝓝 (∑' n, g n)) :=
      hgs.hasSum.tendsto_sum_nat
    have hz : Tendsto (fun K : ℕ => g K) atTop (𝓝 0) := hgs.tendsto_atTop_zero
    have hh := hs.add hz
    simpa only [Finset.sum_range_succ, add_zero] using hh
  have h3 : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, (A n - (n : ℝ)) * (g (n + 1) - g n))
      atTop (𝓝 (∑' n, (A n - (n : ℝ)) * (g (n + 1) - g n))) := hEs.hasSum.tendsto_sum_nat
  have hlim := (h1.sub h2).add h3
  have hzero : ∀ K : ℕ, (∑ n ∈ Finset.range (K + 1), a n * g n)
      - (∑ n ∈ Finset.range (K + 1), g n)
      + (∑ n ∈ Finset.range K, (A n - (n : ℝ)) * (g (n + 1) - g n)) = (A K - (K : ℝ)) * g K := by
    intro K
    have h := abel_identity a g A hA hg0 K
    linarith
  have hEq : (∑' n, a n * g n) - (∑' n, g n)
      + (∑' n, (A n - (n : ℝ)) * (g (n + 1) - g n)) = 0 := by
    refine tendsto_nhds_unique ?_ hC
    simpa only [hzero] using hlim
  have habs := norm_tsum_le_tsum_norm
    (f := fun n => (A n - (n : ℝ)) * (g (n + 1) - g n))
    (by simpa only [Real.norm_eq_abs] using hEabs)
  rw [Real.norm_eq_abs] at habs
  have heq2 : (∑' n, a n * g n) - (∑' n, g n)
      = -(∑' n, (A n - (n : ℝ)) * (g (n + 1) - g n)) := by linarith
  rw [heq2, abs_neg]
  exact habs


/-! ### Summability of the weighted prime number theorem error -/

private lemma summable_log_sq_exp {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => Real.log (n : ℝ) * Real.log (n : ℝ) * Real.exp (-2 * n / N)) := by
  have hsq : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-2 * n / N)) := by
    have h := Real.summable_pow_mul_exp_neg_nat_mul 2 (show (0 : ℝ) < 2 / (N : ℝ) by positivity)
    refine h.congr (fun n => ?_)
    congr 2
    ring
  refine Summable.of_norm_bounded hsq (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hl : Real.log (n : ℝ) ≤ (n : ℝ) := by
      have h' := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (n : ℝ))
      linarith
    have hn0 : 0 ≤ (n : ℝ) := by linarith
    have he : 0 ≤ Real.exp (-2 * (n : ℝ) / N) := (Real.exp_pos _).le
    simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_of_nonneg hl0]
    calc Real.log (n : ℝ) * Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N)
        ≤ ((n : ℝ) * (n : ℝ)) * Real.exp (-2 * (n : ℝ) / N) := by
          apply mul_le_mul_of_nonneg_right _ he
          exact mul_le_mul hl hl hl0 hn0
      _ = (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ) / N) := by ring

private lemma log_nonneg_nat (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

private lemma summable_lambda_log_exp {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n
      * (Real.log (n : ℝ) * Real.exp (-2 * n / N))) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_log_sq_exp hN)
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (log_nonneg_nat n) (Real.exp_pos _).le)
  · have hl := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have hl0 := log_nonneg_nat n
    have he : 0 ≤ Real.exp (-2 * (n : ℝ) / N) := (Real.exp_pos _).le
    calc ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
        = (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ)) * Real.exp (-2 * (n : ℝ) / N) := by ring
      _ ≤ (Real.log (n : ℝ) * Real.log (n : ℝ)) * Real.exp (-2 * (n : ℝ) / N) := by
          apply mul_le_mul_of_nonneg_right _ he
          exact mul_le_mul_of_nonneg_right hl hl0
      _ = Real.log (n : ℝ) * Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N) := by ring

private noncomputable def thetaInc (n : ℕ) : ℝ := if n.Prime then Real.log (n : ℝ) else 0

private lemma thetaInc_nonneg (n : ℕ) : 0 ≤ thetaInc n := by
  unfold thetaInc
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl 0

private lemma thetaInc_le_log (n : ℕ) : thetaInc n ≤ Real.log (n : ℝ) := by
  unfold thetaInc
  split_ifs with h
  · exact le_refl _
  · exact log_nonneg_nat n

private lemma theta_cumulative (n : ℕ) :
    Chebyshev.theta ((n : ℕ) : ℝ) = ∑ i ∈ Finset.range (n + 1), thetaInc i := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter]
  rw [show Finset.Icc 0 n = Finset.range (n + 1) from by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega]
  exact Finset.sum_congr rfl (fun i _ => by unfold thetaInc; rfl)

private lemma summable_thetaInc_log_exp {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * n / N))) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_log_sq_exp hN)
  · exact mul_nonneg (thetaInc_nonneg n) (mul_nonneg (log_nonneg_nat n) (Real.exp_pos _).le)
  · have hl := thetaInc_le_log n
    have hl0 := log_nonneg_nat n
    have he : 0 ≤ Real.exp (-2 * (n : ℝ) / N) := (Real.exp_pos _).le
    calc thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
        = (thetaInc n * Real.log (n : ℝ)) * Real.exp (-2 * (n : ℝ) / N) := by ring
      _ ≤ (Real.log (n : ℝ) * Real.log (n : ℝ)) * Real.exp (-2 * (n : ℝ) / N) := by
          apply mul_le_mul_of_nonneg_right _ he
          exact mul_le_mul_of_nonneg_right hl hl0
      _ = Real.log (n : ℝ) * Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N) := by ring

/-- `log n ≤ 4 √n` and `log²n ≤ 16 √n`. -/
private lemma log_bounds {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ 4 * Real.sqrt (n : ℝ) ∧ (Real.log (n : ℝ)) ^ 2 ≤ 16 * Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnr0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  set u := Real.sqrt (Real.sqrt (n : ℝ)) with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (Real.one_le_sqrt).mpr ((Real.one_le_sqrt).mpr hn1)
  have hu0 : 0 < u := by linarith
  have huu : u ^ 2 = Real.sqrt (n : ℝ) := by rw [hu]; exact Real.sq_sqrt hnr0
  have h4 : u ^ 4 = (n : ℝ) := by
    rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, huu]
    exact Real.sq_sqrt (by positivity)
  have hlog : Real.log (n : ℝ) = 4 * Real.log u := by
    rw [← h4, Real.log_pow]; push_cast; ring
  have hle : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
  have hlu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have h1 : Real.log (n : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by
    rw [hlog, ← huu]
    nlinarith
  refine ⟨h1, ?_⟩
  have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc (Real.log (n : ℝ)) ^ 2 ≤ (4 * u) ^ 2 := by
        rw [hlog]; nlinarith
    _ = 16 * u ^ 2 := by ring
    _ = 16 * Real.sqrt (n : ℝ) := by rw [huu]

/-- A pointwise bound for the Abel error of a sequence `E` bounded by `K1 n e^{-c√log n}`. -/
private lemma abel_error_pointwise {N : ℕ} (hN : 2 ≤ N) {E : ℕ → ℝ} {K1 c Cb : ℝ}
    (hK1 : 0 ≤ K1) (hCb : 0 ≤ Cb) (hc : 0 < c)
    (hCb' : ∀ s : ℝ, 0 ≤ s → s * Real.exp (-c * Real.sqrt s) ≤ Cb)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))))
    (hE0 : E 0 = 0) :
    (∀ n : ℕ, |E n * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ)) / N)
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))|
      ≤ K1 * Real.exp (-2 * (n : ℝ) / N)
        + K1 * (2 * (Cb + 1) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / N))) := by
  intro n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [hE0]
    simp only [Nat.cast_zero, mul_zero, zero_mul, abs_zero, add_zero]
    positivity
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast h)
    have hex : 0 ≤ Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := (Real.exp_pos _).le
    have he : 0 ≤ Real.exp (-2 * (n : ℝ) / (N : ℝ)) := (Real.exp_pos _).le
    have hCbn : Real.log (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ Cb := hCb' _ hlog0
    have hex1 : Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ 1 := by
      calc Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log (n : ℝ)), hc])
        _ = 1 := Real.exp_zero
    have hd := g_diff_bound hN h
    have hE' := hE n h
    have hfac : |E n| * |Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ)) / N)
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N)|
        ≤ (K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))))
          * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / N)) := by
      apply mul_le_mul hE' hd (abs_nonneg _)
      positivity
    rw [abs_mul]
    refine le_trans hfac ?_
    have h1 : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (1 / (n : ℝ))
        * Real.exp (-2 * (n : ℝ) / N) ≤ K1 * Real.exp (-2 * (n : ℝ) / N) := by
      have hid : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (1 / (n : ℝ))
          = K1 * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by
        field_simp
      rw [hid]
      apply mul_le_mul_of_nonneg_right _ he
      nlinarith [hK1, hex1]
    have h2 : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
        * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / N)
        ≤ K1 * (2 * (Cb + 1) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / N)) := by
      have hkey : (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1)
          ≤ (n : ℝ) * (Cb + 1) := by
        have hwe : Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1)
            = Real.log (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
              + Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by ring
        rw [mul_assoc, hwe, mul_add]
        have h1' : (n : ℝ) * (Real.log (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))))
            ≤ (n : ℝ) * Cb := mul_le_mul_of_nonneg_left hCbn hn0.le
        have h2' : (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hex1 hn0.le
        nlinarith [h1', h2']
      have hrew : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
          * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / N)
          = K1 * (2 / (N : ℝ))
            * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1))
            * Real.exp (-2 * (n : ℝ) / N) := by ring
      rw [hrew]
      have hstep : K1 * (2 / (N : ℝ))
          * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1))
          * Real.exp (-2 * (n : ℝ) / N)
          ≤ K1 * (2 / (N : ℝ)) * ((n : ℝ) * (Cb + 1)) * Real.exp (-2 * (n : ℝ) / N) := by
        apply mul_le_mul_of_nonneg_right _ he
        apply mul_le_mul_of_nonneg_left hkey
        positivity
      refine le_trans hstep (le_of_eq ?_)
      ring
    have hsum : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
        * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / N))
        = K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (1 / (n : ℝ))
            * Real.exp (-2 * (n : ℝ) / N)
          + K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
            * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / N) := by
      ring
    rw [hsum]
    linarith [h1, h2]


/-- The weighted `Λ log` moment is `(N/2) log N + O(N)`. -/
private lemma pow_three_exp_summable {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun K : ℕ => (K : ℝ) ^ 3 * Real.exp (-2 * (K : ℝ) / N)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 3 (show (0 : ℝ) < 2 / (N : ℝ) by positivity)
  refine h.congr (fun n => ?_)
  congr 2
  ring

private lemma lambda_log_tsum_asymptotic :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
        - (N : ℝ) / 2 * Real.log (N : ℝ)| ≤ K * (N : ℝ) := by
  obtain ⟨K1, hK1, c, hc, hψ⟩ := psi_error_nat
  obtain ⟨Cb, hCb0, hCb'⟩ := log_mul_exp_neg_sqrt_bounded hc
  obtain ⟨K2, N2, hG⟩ := log_tsum_asymptotic
  refine ⟨K1 * (4 + 2 * Cb) + |K2| + 1, by positivity, max N2 20, fun N hN => ?_⟩
  have hN20 : 20 ≤ N := le_trans (le_max_right _ _) hN
  have hN2' : 2 ≤ N := le_trans (by norm_num) hN20
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN20
  have hGN := hG N (le_trans (le_max_left _ _) hN)
  have hpt := abel_error_pointwise (N := N) hN2'
    (E := fun n => Chebyshev.psi (n : ℝ) - (n : ℝ))
    (K1 := K1) (c := c) (Cb := Cb) (by linarith) hCb0 hc hCb'
    (fun n hn => hψ n hn) (by simp [Chebyshev.psi])
  have hmaj : Summable (fun n : ℕ => K1 * Real.exp (-2 * (n : ℝ) / N)
      + K1 * (2 * (Cb + 1) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / N))) :=
    ((summable_exp_two hN1).mul_left K1).add ((summable_nat_exp hN1).mul_left _)
  have hEabs : Summable (fun n : ℕ => |(Chebyshev.psi (n : ℝ) - (n : ℝ))
      * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt hmaj
  have hEs : Summable (fun n : ℕ => (Chebyshev.psi (n : ℝ) - (n : ℝ))
      * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))) :=
    Summable.of_norm_bounded (by simpa only [Real.norm_eq_abs] using hEabs) (fun n => le_refl _)
  have hCK : ∀ K : ℕ, |(Chebyshev.psi ((K : ℕ) : ℝ) - (K : ℝ))
      * (Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)))|
      ≤ K1 * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))) := by
    intro K
    have hEK : |Chebyshev.psi ((K : ℕ) : ℝ) - (K : ℝ)| ≤ K1 * (K : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos K with h | h
      · subst h; simp [Chebyshev.psi]
      · have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h
        have h1 := hψ K h
        have hex1 : Real.exp (-c * Real.sqrt (Real.log ((K : ℕ) : ℝ))) ≤ 1 := by
          calc Real.exp (-c * Real.sqrt (Real.log ((K : ℕ) : ℝ))) ≤ Real.exp 0 :=
                Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log ((K : ℕ) : ℝ)), hc])
            _ = 1 := Real.exp_zero
        calc |Chebyshev.psi ((K : ℕ) : ℝ) - (K : ℝ)|
            ≤ K1 * (K : ℝ) * Real.exp (-c * Real.sqrt (Real.log ((K : ℕ) : ℝ))) := h1
          _ ≤ K1 * (K : ℝ) * 1 := by
              apply mul_le_mul_of_nonneg_left hex1
              have h0 : (0 : ℝ) ≤ K1 := by linarith
              positivity
          _ = K1 * (K : ℝ) := by ring
          _ ≤ K1 * (K : ℝ) ^ 2 := by
              have h0 : (0 : ℝ) ≤ K1 := by linarith
              have hk : (0 : ℝ) ≤ (K : ℝ) - 1 := by linarith
              have hpos : (0 : ℝ) ≤ (K : ℝ) := by linarith
              nlinarith [mul_nonneg h0 (mul_nonneg hpos hk)]
    have hgK : |Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))|
        ≤ (K : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)) := by
      rw [abs_mul, Real.abs_exp, abs_of_nonneg (log_nonneg_nat K)]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rcases Nat.eq_zero_or_pos K with h | h
      · subst h; simp
      · have := Real.log_le_sub_one_of_pos (by exact_mod_cast h : (0 : ℝ) < (K : ℝ))
        linarith
    rw [abs_mul]
    calc |Chebyshev.psi ((K : ℕ) : ℝ) - (K : ℝ)|
          * |Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))|
        ≤ (K1 * (K : ℝ) ^ 2) * ((K : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))) :=
          mul_le_mul hEK hgK (abs_nonneg _) (by positivity)
      _ = K1 * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))) := by ring
  have hC0 : Tendsto (fun K : ℕ => (Chebyshev.psi ((K : ℕ) : ℝ) - (K : ℝ))
      * (Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)))) atTop (𝓝 0) := by
    have hcube := pow_three_exp_summable hN1
    have hz : Tendsto (fun K : ℕ => K1 * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))))
        atTop (𝓝 0) := by
      have h := hcube.tendsto_atTop_zero
      have h2 := h.const_mul K1
      simpa only [mul_zero] using h2
    have hzn : Tendsto (fun K : ℕ => -(K1 * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)))))
        atTop (𝓝 0) := by
      simpa only [neg_zero] using hz.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hzn hz (fun K => ?_) (fun K => ?_)
    · exact (abs_le.mp (hCK K)).1
    · exact (abs_le.mp (hCK K)).2
  have hab := abel_tsum_error (a := fun n => ArithmeticFunction.vonMangoldt n)
    (A := fun n => Chebyshev.psi (n : ℝ)) (g := fun n => Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
    (fun n => (sum_range_vonMangoldt n).symm) (by simp)
    (summable_lambda_log_exp hN1) (summable_log_exp hN1) hEs hEabs hC0
  have hbound : (∑' n : ℕ, |(Chebyshev.psi (n : ℝ) - (n : ℝ))
      * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))|) ≤ K1 * (4 + 2 * Cb) * (N : ℝ) := by
    refine le_trans (Summable.tsum_le_tsum hpt hEabs hmaj) ?_
    rw [Summable.tsum_add ((summable_exp_two hN1).mul_left K1) ((summable_nat_exp hN1).mul_left _),
      tsum_mul_left, tsum_mul_left]
    have hA := geo_sum_upper hN2'
    have hAn := sum_nat_mul_geo_le hN2'
    have hNr : (20 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN20
    have hKN : (0 : ℝ) ≤ K1 * (N : ℝ) := by positivity
    have h1 : K1 * (∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N)) ≤ K1 * (N : ℝ) := by
      have hA' : (∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N)) ≤ (N : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left hA' (by linarith)
    have h2 : K1 * (2 * (Cb + 1) / (N : ℝ)) * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
        ≤ K1 * (2 * (Cb + 1)) * (N : ℝ) := by
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      have h3 : (2 * (Cb + 1) / (N : ℝ)) * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
          ≤ (2 * (Cb + 1) / (N : ℝ)) * (N : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hAn
        positivity
      have h4 : (2 * (Cb + 1) / (N : ℝ)) * (N : ℝ) ^ 2 = 2 * (Cb + 1) * (N : ℝ) := by
        field_simp
      rw [h4] at h3
      calc K1 * (2 * (Cb + 1) / (N : ℝ)) * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
          = K1 * ((2 * (Cb + 1) / (N : ℝ)) * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))) := by ring
        _ ≤ K1 * (2 * (Cb + 1) * (N : ℝ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = K1 * (2 * (Cb + 1)) * (N : ℝ) := by ring
    have hle3 : K1 * (∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N))
        + K1 * (2 * (Cb + 1) / (N : ℝ)) * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
        ≤ K1 * (4 + 2 * Cb) * (N : ℝ) := by
      have hlea : K1 * (N : ℝ) * (3 + 2 * Cb) ≤ K1 * (N : ℝ) * (4 + 2 * Cb) :=
        mul_le_mul_of_nonneg_left (by linarith : (3 : ℝ) + 2 * Cb ≤ 4 + 2 * Cb) hKN
      have hform : K1 * (N : ℝ) + K1 * (2 * (Cb + 1)) * (N : ℝ) = K1 * (N : ℝ) * (3 + 2 * Cb) := by ring
      have hform2 : K1 * (N : ℝ) * (4 + 2 * Cb) = K1 * (4 + 2 * Cb) * (N : ℝ) := by ring
      calc K1 * (∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N))
            + K1 * (2 * (Cb + 1) / (N : ℝ)) * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
          ≤ K1 * (N : ℝ) + K1 * (2 * (Cb + 1)) * (N : ℝ) := add_le_add h1 h2
        _ = K1 * (N : ℝ) * (3 + 2 * Cb) := hform
        _ ≤ K1 * (N : ℝ) * (4 + 2 * Cb) := hlea
        _ = K1 * (4 + 2 * Cb) * (N : ℝ) := hform2
    exact hle3
  have hMG : |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
      - (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N))| ≤ K1 * (4 + 2 * Cb) * (N : ℝ) :=
    le_trans hab hbound
  have hGN' : |(∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
      - (N : ℝ) / 2 * Real.log (N : ℝ)| ≤ (|K2| + 1) * (N : ℝ) := by
    have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hle : K2 ≤ |K2| + 1 := by linarith [le_abs_self K2]
    have := mul_le_mul_of_nonneg_right hle hNn
    linarith [hGN, this]
  have htri : |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
      - (N : ℝ) / 2 * Real.log (N : ℝ)|
      ≤ |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
        - (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N))|
        + |(∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N)) - (N : ℝ) / 2 * Real.log (N : ℝ)| := by
    have he : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
        - (N : ℝ) / 2 * Real.log (N : ℝ)
        = ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
          - (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N)))
          + ((∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N)) - (N : ℝ) / 2 * Real.log (N : ℝ)) := by
      ring
    rw [he]
    exact abs_add_le _ _
  linarith [htri, hMG, hGN', hCb0, hK1, hN20]


/-! ### The two Abel asymptotics for the weighted log-moment -/

private lemma sqrt_mul_log_sq_le {N : ℕ} (hN : 2 ≤ N) {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
        * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
      ≤ 8 * Real.exp (-2 * (n : ℝ) / (N : ℝ))
        + (80 / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
  obtain ⟨h1, h2⟩ := log_bounds hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  have hl0 : 0 ≤ Real.log (n : ℝ) := log_nonneg_nat n
  have he : 0 ≤ Real.exp (-2 * (n : ℝ) / (N : ℝ)) := (Real.exp_pos _).le
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (1 / (n : ℝ))
      ≤ 8 := by
    have : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (1 / (n : ℝ))
        = 2 * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) := by
      field_simp
      nlinarith [hsq]
    rw [this]
    have h3 : Real.log (n : ℝ) / Real.sqrt (n : ℝ) ≤ 4 := by
      rw [div_le_iff₀ hsqrt]
      linarith
    linarith
  have hB : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1))
      ≤ (80 / (N : ℝ)) * (n : ℝ) := by
    have hnlog : Real.sqrt (n : ℝ) * (Real.log (n : ℝ) * (Real.log (n : ℝ) + 1))
        ≤ 20 * (n : ℝ) := by
      have hpos : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrt
      have hl1 : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 4 * (n : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hpos
        calc Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) * (4 * Real.sqrt (n : ℝ)) := this
          _ = 4 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
          _ = 4 * (n : ℝ) := by rw [hsq]
      have hl2 : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 2 ≤ 16 * (n : ℝ) := by
        have := mul_le_mul_of_nonneg_left h2 hpos
        calc Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) * (16 * Real.sqrt (n : ℝ)) := this
          _ = 16 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
          _ = 16 * (n : ℝ) := by rw [hsq]
      have hxe : Real.sqrt (n : ℝ) * (Real.log (n : ℝ) * (Real.log (n : ℝ) + 1))
          = Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 2 + Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by ring
      rw [hxe]
      linarith [hl1, hl2]
    rw [show 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1))
        = (4 / (N : ℝ)) * (Real.sqrt (n : ℝ) * (Real.log (n : ℝ) * (Real.log (n : ℝ) + 1))) by ring]
    rw [show (80 / (N : ℝ)) * (n : ℝ) = (4 / (N : ℝ)) * (20 * (n : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left hnlog (by positivity)
  have hexpand : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
      * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
      = (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (1 / (n : ℝ))) * Real.exp (-2 * (n : ℝ) / (N : ℝ))
        + (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)))
          * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by ring
  rw [hexpand]
  have hAb : (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (1 / (n : ℝ))) * Real.exp (-2 * (n : ℝ) / (N : ℝ))
      ≤ 8 * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
    have h0 : 0 ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (1 / (n : ℝ)) := by positivity
    nlinarith [hA, he, h0]
  have hBb : (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)))
      * Real.exp (-2 * (n : ℝ) / (N : ℝ))
      ≤ (80 / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
    have h0 : 0 ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) := by
      have : 0 ≤ 2 / (N : ℝ) * (Real.log (n : ℝ) + 1) := by positivity
      positivity
    calc (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)))
        * Real.exp (-2 * (n : ℝ) / (N : ℝ))
        ≤ ((80 / (N : ℝ)) * (n : ℝ)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hB he
      _ = (80 / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by ring
  linarith [hAb, hBb]


/-- The weighted prime-restricted `log` moment is `(N/2) log N + O(N)`. -/
private lemma theta_log_tsum_asymptotic :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑' n : ℕ, thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
        - (N : ℝ) / 2 * Real.log (N : ℝ)| ≤ K * (N : ℝ) := by
  obtain ⟨K1, hK1, c, hc, hθ⟩ := theta_error_nat
  obtain ⟨Cb, hCb0, hCb'⟩ := log_mul_exp_neg_sqrt_bounded hc
  obtain ⟨K2, N2, hG⟩ := log_tsum_asymptotic
  set Kt : ℝ := K1 * (4 + 2 * Cb) + 100 with hKt
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  refine ⟨Kt + |K2| + 1, by positivity, max N2 20, fun N hN => ?_⟩
  have hN20 : 20 ≤ N := le_trans (le_max_right _ _) hN
  have hN2' : 2 ≤ N := le_trans (by norm_num) hN20
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN20
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hGN := hG N (le_trans (le_max_left _ _) hN)
  -- the pointwise majorant
  have hpt : ∀ n : ℕ, |(Chebyshev.theta (n : ℝ) - (n : ℝ))
      * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))|
      ≤ (K1 + 8) * Real.exp (-2 * (n : ℝ) / N)
        + ((2 * K1 * (Cb + 1) + 80) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / N)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hz : Chebyshev.theta ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) = 0 := by
        rw [Chebyshev.theta_eq_zero_of_lt_two (by norm_num)]
        norm_num
      rw [hz]
      simp only [Nat.cast_zero, Nat.cast_one, sub_zero, mul_zero, zero_mul, abs_zero, add_zero]
      have h1 : (0 : ℝ) ≤ (K1 + 8) * Real.exp (-2 * ((0 : ℕ) : ℝ) / (N : ℝ)) := by positivity
      have h2 : (0 : ℝ) ≤ ((2 * K1 * (Cb + 1) + 80) / (N : ℝ))
          * ((0 : ℝ) * Real.exp (-2 * ((0 : ℕ) : ℝ) / (N : ℝ))) := by
        rw [zero_mul, mul_zero]
      linarith
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast h)
      have hex : 0 ≤ Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := (Real.exp_pos _).le
      have he : 0 ≤ Real.exp (-2 * (n : ℝ) / (N : ℝ)) := (Real.exp_pos _).le
      have hCbn : Real.log (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ Cb := hCb' _ hlog0
      have hex1 : Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ 1 := by
        calc Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log (n : ℝ)), hc])
          _ = 1 := Real.exp_zero
      have hd := g_diff_bound hN2' h
      have hE' := hθ n h
      have hYnn : 0 ≤ (1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1))
          * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by positivity
      have hfac : |(Chebyshev.theta (n : ℝ) - (n : ℝ))
          * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
            - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))|
          ≤ (K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
              + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
            * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
        rw [abs_mul]
        exact mul_le_mul hE' hd (abs_nonneg _) (by positivity)
      refine le_trans hfac ?_
      -- the pure PNT part
      have hpart1 : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
          * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
          ≤ K1 * Real.exp (-2 * (n : ℝ) / (N : ℝ))
            + K1 * (2 * (Cb + 1) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
        have h1 : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (1 / (n : ℝ))
            * Real.exp (-2 * (n : ℝ) / (N : ℝ)) ≤ K1 * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
          have hid : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (1 / (n : ℝ))
              = K1 * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by field_simp
          rw [hid]
          exact mul_le_mul_of_nonneg_right (by nlinarith [hK1, hex1]) he
        have h2 : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
            * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ))
            ≤ K1 * (2 * (Cb + 1) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
          have hkey : (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1)
              ≤ (n : ℝ) * (Cb + 1) := by
            have hwe : Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1)
                = Real.log (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
                  + Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) := by ring
            rw [mul_assoc, hwe, mul_add]
            have h1' : (n : ℝ) * (Real.log (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))))
                ≤ (n : ℝ) * Cb := mul_le_mul_of_nonneg_left hCbn hn0.le
            have h2' : (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ (n : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hex1 hn0.le
            nlinarith [h1', h2']
          have hrew : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
              * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ))
              = K1 * (2 / (N : ℝ))
                * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1))
                * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by ring
          rw [hrew]
          have hstep : K1 * (2 / (N : ℝ))
              * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (Real.log (n : ℝ) + 1))
              * Real.exp (-2 * (n : ℝ) / (N : ℝ))
              ≤ K1 * (2 / (N : ℝ)) * ((n : ℝ) * (Cb + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ he
            apply mul_le_mul_of_nonneg_left hkey
            positivity
          refine le_trans hstep (le_of_eq ?_)
          ring
        have hsum : K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
            * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
            = K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) * (1 / (n : ℝ))
                * Real.exp (-2 * (n : ℝ) / (N : ℝ))
              + K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
                * (2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
          ring
        rw [hsum]
        linarith [h1, h2]
      have hpart2 := sqrt_mul_log_sq_le hN2' h
      have hexpand : (K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
              + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
            * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
          = K1 * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
              * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
            + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
              * ((1 / (n : ℝ) + 2 / (N : ℝ) * (Real.log (n : ℝ) + 1)) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
        ring
      rw [hexpand]
      have hfin : K1 * (2 * (Cb + 1) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
          + (80 / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
          = ((2 * K1 * (Cb + 1) + 80) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
        field_simp
      linarith [hpart1, hpart2, hfin]
  have hmaj : Summable (fun n : ℕ => (K1 + 8) * Real.exp (-2 * (n : ℝ) / N)
      + ((2 * K1 * (Cb + 1) + 80) / (N : ℝ)) * ((n : ℝ) * Real.exp (-2 * (n : ℝ) / N))) :=
    ((summable_exp_two hN1).mul_left _).add ((summable_nat_exp hN1).mul_left _)
  have hEabs : Summable (fun n : ℕ => |(Chebyshev.theta (n : ℝ) - (n : ℝ))
      * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt hmaj
  have hEs : Summable (fun n : ℕ => (Chebyshev.theta (n : ℝ) - (n : ℝ))
      * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))) :=
    Summable.of_norm_bounded (by simpa only [Real.norm_eq_abs] using hEabs) (fun n => le_refl _)
  have hCK : ∀ K : ℕ, |(Chebyshev.theta ((K : ℕ) : ℝ) - (K : ℝ))
      * (Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)))|
      ≤ Kt * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))) := by
    intro K
    have hEK : |Chebyshev.theta ((K : ℕ) : ℝ) - (K : ℝ)| ≤ Kt * (K : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos K with h | h
      · subst h
        rw [Chebyshev.theta_eq_zero_of_lt_two (by norm_num)]
        norm_num
      · have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h
        have h1 := hθ K h
        have hex1 : Real.exp (-c * Real.sqrt (Real.log ((K : ℕ) : ℝ))) ≤ 1 := by
          calc Real.exp (-c * Real.sqrt (Real.log ((K : ℕ) : ℝ))) ≤ Real.exp 0 :=
                Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log ((K : ℕ) : ℝ)), hc])
            _ = 1 := Real.exp_zero
        have hlogb := (log_bounds h).1
        have hsq : Real.sqrt ((K : ℕ) : ℝ) ≤ (K : ℝ) := by
          calc Real.sqrt ((K : ℕ) : ℝ) ≤ Real.sqrt ((K : ℝ) * (K : ℝ)) := by
                apply Real.sqrt_le_sqrt; nlinarith [hKr]
            _ = (K : ℝ) := Real.sqrt_mul_self (by linarith)
        have hs0 : (0 : ℝ) ≤ Real.sqrt ((K : ℕ) : ℝ) := Real.sqrt_nonneg _
        have hstep1 : K1 * (K : ℝ) * Real.exp (-c * Real.sqrt (Real.log ((K : ℕ) : ℝ)))
            ≤ K1 * (K : ℝ) := by
          calc K1 * (K : ℝ) * Real.exp (-c * Real.sqrt (Real.log ((K : ℕ) : ℝ)))
              ≤ K1 * (K : ℝ) * 1 := by
                apply mul_le_mul_of_nonneg_left hex1
                have h0 : (0 : ℝ) ≤ K1 := by linarith
                positivity
            _ = K1 * (K : ℝ) := by ring
        have hstep2 : 2 * Real.sqrt ((K : ℕ) : ℝ) * Real.log ((K : ℕ) : ℝ) ≤ 8 * (K : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left hlogb (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt ((K : ℕ) : ℝ))
          have hsq2 : Real.sqrt ((K : ℕ) : ℝ) * Real.sqrt ((K : ℕ) : ℝ) = (K : ℝ) :=
            Real.mul_self_sqrt (by positivity)
          linarith [hmul, hsq2]
        have hfin : K1 * (K : ℝ) + 8 * (K : ℝ) ≤ Kt * (K : ℝ) ^ 2 := by
          rw [hKt]
          have hK0 : (0 : ℝ) ≤ (K : ℝ) := by linarith
          have hcoef : K1 + 8 ≤ K1 * (4 + 2 * Cb) + 100 := by nlinarith [hK1, hCb0]
          have hposc : (0 : ℝ) ≤ K1 * (4 + 2 * Cb) + 100 := by nlinarith [hK1, hCb0]
          have hk1 : (0 : ℝ) ≤ (K : ℝ) - 1 := by linarith
          have hs1 : (K1 + 8) * (K : ℝ) ≤ (K1 * (4 + 2 * Cb) + 100) * (K : ℝ) :=
            mul_le_mul_of_nonneg_right hcoef hK0
          have hs2 : (K1 * (4 + 2 * Cb) + 100) * (K : ℝ)
              ≤ (K1 * (4 + 2 * Cb) + 100) * (K : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hK0 hk1]) hposc
          nlinarith [hs1, hs2]
        linarith [h1, hstep1, hstep2, hfin]
    have hgK : |Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))|
        ≤ (K : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)) := by
      rw [abs_mul, Real.abs_exp, abs_of_nonneg (log_nonneg_nat K)]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rcases Nat.eq_zero_or_pos K with h | h
      · subst h; simp
      · have := Real.log_le_sub_one_of_pos (by exact_mod_cast h : (0 : ℝ) < (K : ℝ))
        linarith
    rw [abs_mul]
    calc |Chebyshev.theta ((K : ℕ) : ℝ) - (K : ℝ)|
          * |Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))|
        ≤ (Kt * (K : ℝ) ^ 2) * ((K : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))) :=
          mul_le_mul hEK hgK (abs_nonneg _) (by positivity)
      _ = Kt * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))) := by ring
  have hC0 : Tendsto (fun K : ℕ => (Chebyshev.theta ((K : ℕ) : ℝ) - (K : ℝ))
      * (Real.log ((K : ℕ) : ℝ) * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)))) atTop (𝓝 0) := by
    have hcube := pow_three_exp_summable hN1
    have hz : Tendsto (fun K : ℕ => Kt * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ))))
        atTop (𝓝 0) := by
      have h := hcube.tendsto_atTop_zero
      have h2 := h.const_mul Kt
      simpa only [mul_zero] using h2
    have hzn : Tendsto (fun K : ℕ => -(Kt * ((K : ℝ) ^ 3 * Real.exp (-2 * ((K : ℕ) : ℝ) / (N : ℝ)))))
        atTop (𝓝 0) := by
      simpa only [neg_zero] using hz.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hzn hz (fun K => ?_) (fun K => ?_)
    · exact (abs_le.mp (hCK K)).1
    · exact (abs_le.mp (hCK K)).2
  have hab := abel_tsum_error (a := thetaInc)
    (A := fun n => Chebyshev.theta (n : ℝ)) (g := fun n => Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
    (fun n => theta_cumulative n) (by simp)
    (summable_thetaInc_log_exp hN1) (summable_log_exp hN1) hEs hEabs hC0
  have hbound : (∑' n : ℕ, |(Chebyshev.theta (n : ℝ) - (n : ℝ))
      * (Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) / (N : ℝ))
        - Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))|) ≤ Kt * (N : ℝ) := by
    refine le_trans (Summable.tsum_le_tsum hpt hEabs hmaj) ?_
    rw [Summable.tsum_add ((summable_exp_two hN1).mul_left _) ((summable_nat_exp hN1).mul_left _),
      tsum_mul_left, tsum_mul_left]
    have hA := geo_sum_upper hN2'
    have hAn := sum_nat_mul_geo_le hN2'
    have hNr : (20 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN20
    have h1 : (K1 + 8) * (∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N)) ≤ (K1 + 8) * ((N : ℝ) / 2 + 1) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have h2 : ((2 * K1 * (Cb + 1) + 80) / (N : ℝ))
        * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
        ≤ (2 * K1 * (Cb + 1) + 80) * (N : ℝ) := by
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      have h3 : (2 * K1 * (Cb + 1) + 80) / (N : ℝ) * (N : ℝ) ^ 2
          = (2 * K1 * (Cb + 1) + 80) * (N : ℝ) := by field_simp
      calc ((2 * K1 * (Cb + 1) + 80) / (N : ℝ))
            * (∑' n : ℕ, (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
          ≤ ((2 * K1 * (Cb + 1) + 80) / (N : ℝ)) * (N : ℝ) ^ 2 := by
            apply mul_le_mul_of_nonneg_left hAn; positivity
        _ = (2 * K1 * (Cb + 1) + 80) * (N : ℝ) := h3
    rw [hKt]
    nlinarith [h1, h2, hK1, hCb0, hNr]
  have hMG : |(∑' n : ℕ, thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
      - (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N))| ≤ Kt * (N : ℝ) := le_trans hab hbound
  have hGN' : |(∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / N))
      - (N : ℝ) / 2 * Real.log (N : ℝ)| ≤ (|K2| + 1) * (N : ℝ) := by
    have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hle : K2 ≤ |K2| + 1 := by linarith [le_abs_self K2]
    have := mul_le_mul_of_nonneg_right hle hNn
    linarith [hGN, this]
  have htri : |(∑' n : ℕ, thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
      - (N : ℝ) / 2 * Real.log (N : ℝ)|
      ≤ |(∑' n : ℕ, thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
        - (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N))|
        + |(∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N)) - (N : ℝ) / 2 * Real.log (N : ℝ)| := by
    have he : (∑' n : ℕ, thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
        - (N : ℝ) / 2 * Real.log (N : ℝ)
        = ((∑' n : ℕ, thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * n / N)))
          - (∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N)))
          + ((∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-2 * n / N)) - (N : ℝ) / 2 * Real.log (N : ℝ)) := by
      ring
    rw [he]
    exact abs_add_le _ _
  linarith [htri, hMG, hGN', hKt0, hN20]


end J209

/-- LEAF arXiv:1606.00869v2 page 3, using PNT. Bound the sum using Prime Number Theorem. -/
theorem lemma3_raw_moment_asymptotic : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * n / N)) - N / 2 * Real.log N| ≤ K * N := by
  obtain ⟨K1, hK1, N1, hM⟩ := J209.lambda_log_tsum_asymptotic
  obtain ⟨K2, hK2, N2, hP⟩ := J209.theta_log_tsum_asymptotic
  refine ⟨K1 + K2, max (max N1 N2) 20, fun N hN => ?_⟩
  have hN20 : 20 ≤ N := le_trans (le_max_right _ _) hN
  have hN1' : 1 ≤ N := le_trans (by norm_num) hN20
  have hN1le : N1 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2le : N2 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hM' := hM N hN1le
  have hP' := hP N hN2le
  have hSm : (∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
      ≤ ∑' n : ℕ, Λ n * (Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by
    apply Summable.tsum_le_tsum
    · intro n
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hl := ArithmeticFunction.vonMangoldt_le_log (n := n)
      have he : 0 ≤ Real.exp (-2 * (n : ℝ) / (N : ℝ)) := (Real.exp_pos _).le
      calc Λ n ^ 2 * Real.exp (-2 * (n : ℝ) / (N : ℝ))
          = (Λ n * Λ n) * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by ring
        _ ≤ (Λ n * Real.log (n : ℝ)) * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ he
            exact mul_le_mul_of_nonneg_left hl h0
        _ = Λ n * (Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))) := by ring
    · exact summable_lambda_sq_exp hN1'
    · exact J209.summable_lambda_log_exp hN1'
  have hPS : (∑' n : ℕ, J209.thetaInc n * (Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ))))
      ≤ ∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by
    apply Summable.tsum_le_tsum
    · intro n
      by_cases hp : n.Prime
      · have hΛ : Λ n = Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_apply_prime hp
        have hinc : J209.thetaInc n = Real.log (n : ℝ) := by
          unfold J209.thetaInc
          rw [if_pos hp]
        rw [hinc, hΛ]
        have heq : Real.log (n : ℝ) * (Real.log (n : ℝ) * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
            = Real.log (n : ℝ) ^ 2 * Real.exp (-2 * (n : ℝ) / (N : ℝ)) := by ring
        rw [heq]
      · have hinc : J209.thetaInc n = 0 := by
          unfold J209.thetaInc
          rw [if_neg hp]
        rw [hinc, zero_mul]
        exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    · exact J209.summable_thetaInc_log_exp hN1'
    · exact summable_lambda_sq_exp hN1'
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hSle : (∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
      - (N : ℝ) / 2 * Real.log (N : ℝ) ≤ (K1 + K2) * (N : ℝ) := by
    have := abs_le.mp hM'
    nlinarith [this.2, hSm]
  have hSge : -((K1 + K2) * (N : ℝ)) ≤ (∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * (n : ℝ) / (N : ℝ)))
      - (N : ℝ) / 2 * Real.log (N : ℝ) := by
    have := abs_le.mp hP'
    nlinarith [this.1, hPS, hK1, hK2, hNnonneg]
  exact abs_le.mpr ⟨hSge, hSle⟩

/-- LEAF arXiv:1606.00869v2 page 3, Parseval step bounds -/
theorem lemma3_parseval_bound : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N))
      - N / 2 * Real.log N| ≤ K * N :=
  lemma3_moment_of_square_moment lemma3_raw_moment_asymptotic

/-- LEAF arXiv:1606.00869v2 page 3, Parseval step exact moment -/
theorem lemma3_parseval_exact_moment : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖St N α - 1 / zz N α‖ ^ 2) - N / 2 * Real.log N|
      ≤ K * N * Real.sqrt (Real.log N) := by
  have := lemma3_of_moment lemma3_parseval_bound
  unfold Lemma3 at this
  exact this

/-- The exact Lemma3 Prop is conditional on the raw square moment alone. -/
theorem lz_lemma3_decomp_assembly : Lemma3 :=
  lemma3_of_square_moment lemma3_raw_moment_asymptotic

end LeanLab.LZCesaroShort
