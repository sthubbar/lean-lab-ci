/-
The printed Lemma 2.8 of Wu 1993 is FALSE.

J. Wu, Theoremes generalises de Bombieri-Vinogradov dans les petits intervalles,
Quart. J. Math. Oxford 44 (1993), 109 to 128, papers/Wu1993.pdf, page 116:

  LEMME 2.8. Soient a_j(n) (1 <= j <= k) des fonctions arithmetiques verifiant
  les conditions suivantes
      sum_{n <= x} |a_j(n)|^2 / n  <<  L^{lambda_j}
  pour des constantes lambda_j > 0 (1 <= j <= k), on a alors
      sum_{n <= x} |(a_1 * ... * a_k)(n)|^2 / n  <<  L^{lambda_1 + ... + lambda_k},
  L = log x, * the Dirichlet convolution. "La demonstration de ce lemme est triviale."

Here `*` is the Dirichlet convolution, which is the only reading under which the lemma has
content: for the pointwise product the conclusion is Cauchy-Schwarz in the weights 1 (or
1/n) and needs no hypothesis at all, while on page 123 the lemma bounds the coefficients of
a product of Dirichlet polynomials, F(s) = product of the F_k(s), whose coefficients are
convolved, and it is there that the lemma is applied.

The lemma is false, and the defect is in the exponent, not in a constant. Take k = 2
and a_1 = a_2 = 1, the constant function 1. Its hypothesis holds with lambda_1 =
lambda_2 = 1, since sum_{n <= x} 1/n <= 1 + log x (`one_hypothesis_wu_lemma28`). The
convolution a_1 * a_2 is then the divisor function tau(n) = (n.divisors).card, so the
conclusion of the printed lemma would read

      sum_{n <= x} tau(n)^2 / n  <<  L^2.

But sum_{n <= N} tau(n)/n >= H_M^2 with M = floor(sqrt N) (the pairs d e with
d, e <= M all satisfy d e <= N, so sum_{n <= N} tau(n)/n = sum_{d e <= N} 1/(d e)
contains H_M^2), and Cauchy-Schwarz in the form sum f^2/g >= (sum f)^2 / (sum g)
(`Finset.sq_sum_div_le_sum_sq_div`) with f = tau(n)/n, g = 1/n gives

      sum_{n <= N} tau(n)^2 / n  >=  H_M^4 / (1 + log N)  >=  (log N)^3 / C,

which is of order L^3, not L^2, and contradicts every bound K L^2 for large N.
That lower bound is all the refutation uses. For the record the true size of
sum_{n <= x} tau(n)^2/n is of order L^4: the Dirichlet series of tau(n)^2/n is
zeta(1+s)^4 / zeta(2+2s), which has a pole of order four at s = 0, so Perron gives
sum_{n <= x} tau(n)^2/n = log(x)^4 / (4 pi^2) + O(log(x)^3); a sieve to 2*10^7
gives the values 0.0653, 0.0572, 0.0518 and 0.0505 for the ratio to log(x)^4 at
x = 10^5, 10^6, 10^7 and 2*10^7, decreasing towards 1/(4 pi^2) = 0.02533.
So Wu's printed Lemma 2.8 fails here by two powers of log, not one.

A correction replacing L^{lambda_1 + ... + lambda_k} by L^{k(lambda_1 + ... + lambda_k)}
would cover this case, but no proof of that shape is given in Wu 1993: the lemma is
applied on page 123 only for f, g coming from Dirichlet polynomials.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

open Finset Real

namespace LeanLab.Cai2002

/-! ### The harmonic sum as a real number -/

/-- The real sum `sum_{i=1}^{M} 1/i` is the rational `harmonic M`, cast to `ℝ`. -/
private theorem sum_inv_Icc_eq_harmonic (M : ℕ) :
    ∑ i ∈ Icc 1 M, ((i : ℝ))⁻¹ = (harmonic M : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  exact sum_congr rfl (fun i _ => by simp)

/-! ### The divisor function -/

/-- For `1 ≤ n ≤ N` the divisors of `n` are exactly the divisors of `n` in `Icc 1 N`. -/
private theorem divisors_eq_filter_Icc {N n : ℕ} (hn : n ∈ Icc 1 N) :
    n.divisors = (Icc 1 N).filter (fun d => d ∣ n) := by
  have hn1 : 0 < n := (mem_Icc.mp hn).1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn1, (Nat.le_of_dvd hn1 hdvd).trans (mem_Icc.mp hn).2⟩, hdvd⟩
  · rintro ⟨⟨-, -⟩, hdvd⟩
    exact ⟨hdvd, by omega⟩

/-- The divisor count of `n`, `(n.divisors).card`, as a sum of indicators over `Icc 1 N`. -/
private theorem card_divisors_eq_sum {N n : ℕ} (hn : n ∈ Icc 1 N) :
    ((n.divisors.card : ℕ) : ℝ) = ∑ d ∈ Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) := by
  rw [divisors_eq_filter_Icc hn, ← sum_filter]
  simp

/-! ### A lower bound for `sum tau(n)/n` -/

/-- `H_M^2 ≤ sum_{n <= N} tau(n)/n` whenever `M * M ≤ N`: the left side is the sum of
`1/(d e)` over `d, e ≤ M`, and every `d e` there is at most `N`, with `1/(d e)` the
`1/n` term of the divisor sum at `n = d e`. -/
private theorem harmonic_sq_le_tau_div_sum (N M : ℕ) (hMN : M * M ≤ N) :
    (∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹) ^ 2 ≤
      ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / n := by
  classical
  have hle : M ≤ N := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · omega
    · calc M = M * 1 := (mul_one M).symm
        _ ≤ M * M := Nat.mul_le_mul_left M hM
        _ ≤ N := hMN
  have hsq : (∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹) ^ 2 =
      ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, (((d * e : ℕ)) : ℝ)⁻¹ := by
    rw [sq, sum_mul_sum]
    exact sum_congr rfl (fun d _ => sum_congr rfl (fun e _ => by push_cast; rw [mul_inv]))
  have himg : ∀ d ∈ Icc 1 M,
      ∑ e ∈ Icc 1 M, (((d * e : ℕ)) : ℝ)⁻¹ ≤
        ∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n), ((n : ℝ))⁻¹ := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    have hdM : d ≤ M := (mem_Icc.mp hd).2
    have hinj : ∀ e₁ ∈ Icc 1 M, ∀ e₂ ∈ Icc 1 M, d * e₁ = d * e₂ → e₁ = e₂ := by
      intro e₁ _ e₂ _ h
      exact Nat.eq_of_mul_eq_mul_left (by omega) h
    have hsub : (Icc 1 M).image (fun e => d * e) ⊆ (Icc 1 N).filter (fun n => d ∣ n) := by
      intro n hn
      obtain ⟨e, he, rfl⟩ := mem_image.mp hn
      have heM : e ≤ M := (mem_Icc.mp he).2
      have he1 : 1 ≤ e := (mem_Icc.mp he).1
      have hde1 : 1 ≤ d * e :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by exact_mod_cast hde1, ?_⟩, dvd_mul_right d e⟩
      calc d * e ≤ M * M := Nat.mul_le_mul hdM heM
        _ ≤ N := hMN
    calc ∑ e ∈ Icc 1 M, (((d * e : ℕ)) : ℝ)⁻¹
        = ∑ n ∈ (Icc 1 M).image (fun e => d * e), ((n : ℝ))⁻¹ := by
          rw [Finset.sum_image]
          exact hinj
      _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n), ((n : ℝ))⁻¹ :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  calc (∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹) ^ 2
      = ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, (((d * e : ℕ)) : ℝ)⁻¹ := hsq
    _ ≤ ∑ d ∈ Icc 1 M, ∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n), ((n : ℝ))⁻¹ :=
        sum_le_sum himg
    _ = ∑ d ∈ Icc 1 M, ∑ n ∈ Icc 1 N, (if d ∣ n then ((n : ℝ))⁻¹ else 0) := by
        refine sum_congr rfl (fun d _ => ?_)
        rw [sum_filter]
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 M, (if d ∣ n then ((n : ℝ))⁻¹ else 0) := sum_comm ..
    _ ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, (if d ∣ n then ((n : ℝ))⁻¹ else 0) := by
        refine sum_le_sum (fun n _ => ?_)
        exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hle)
          (fun _ _ _ => by positivity)
    _ = ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / n := by
        refine sum_congr rfl (fun n hn => ?_)
        rw [card_divisors_eq_sum hn, sum_div]
        refine sum_congr rfl (fun d _ => ?_)
        split_ifs <;> simp

/-! ### A lower bound for `sum tau(n)^2/n` -/

/-- Cauchy-Schwarz with weights: `(sum tau(n)/n)^2 / (sum 1/n) ≤ sum tau(n)^2/n`. -/
private theorem tau_sq_div_sum_ge (N M : ℕ) (hN2 : 2 ≤ N) (hMN : M * M ≤ N) :
    (∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹) ^ 4 / (1 + log N) ≤
      ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 2 / n := by
  classical
  have hlogN0 : 0 ≤ log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hS3pos : 0 < ∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹ := by
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    norm_num
  have htitu : (∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / n) ^ 2 /
      (∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹) ≤
        ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 2 / n := by
    have hmain := Finset.sq_sum_div_le_sum_sq_div (Icc 1 N)
      (fun n => ((n.divisors.card : ℕ) : ℝ) / n)
      (g := fun n => ((n : ℝ))⁻¹)
      (fun n hn => by
        have hn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
        positivity)
    refine hmain.trans_eq ?_
    refine sum_congr rfl (fun n hn => ?_)
    have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by
      have := (mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    field_simp
  have hS3le : (∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹) ≤ 1 + log N := by
    rw [sum_inv_Icc_eq_harmonic]
    exact harmonic_le_one_add_log N
  have hS1 := harmonic_sq_le_tau_div_sum N M hMN
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + log N)]
  calc (∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹) ^ 4
      = ((∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹) ^ 2) ^ 2 := by ring
    _ ≤ (∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / n) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hS1 2
    _ ≤ (∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 2 / n) *
          (∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹) :=
        (div_le_iff₀ hS3pos).mp htitu
    _ ≤ (∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 2 / n) * (1 + log N) := by
        refine mul_le_mul_of_nonneg_left hS3le ?_
        positivity

/-! ### The harmonic sum beats a quarter of the logarithm -/

/-- `log N / 4 ≤ H_{floor sqrt N}` for `N ≥ 16`. -/
private theorem quarter_log_le_harmonic_sqrt (N : ℕ) (hN : 16 ≤ N) :
    log N / 4 ≤ ∑ d ∈ Icc 1 ⌊Real.sqrt (N : ℝ)⌋₊, ((d : ℝ))⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hst := log_le_harmonic_floor (Real.sqrt (N : ℝ) / 2) (by positivity)
  have hst' : log (Real.sqrt (N : ℝ) / 2) ≤
      ∑ d ∈ Icc 1 ⌊Real.sqrt (N : ℝ) / 2⌋₊, ((d : ℝ))⁻¹ := by
    rw [sum_inv_Icc_eq_harmonic]
    exact hst
  have hmono : ⌊Real.sqrt (N : ℝ) / 2⌋₊ ≤ ⌊Real.sqrt (N : ℝ)⌋₊ :=
    Nat.floor_mono (by linarith)
  have h2 : ∑ d ∈ Icc 1 ⌊Real.sqrt (N : ℝ) / 2⌋₊, ((d : ℝ))⁻¹ ≤
      ∑ d ∈ Icc 1 ⌊Real.sqrt (N : ℝ)⌋₊, ((d : ℝ))⁻¹ :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmono) (fun _ _ _ => by positivity)
  have hlog : log N / 4 ≤ log (Real.sqrt (N : ℝ) / 2) := by
    rw [log_div hsq.ne' (by norm_num), log_sqrt hNpos.le]
    have h16 : Real.log 16 ≤ Real.log (N : ℝ) :=
      log_le_log (by norm_num) (by exact_mod_cast hN)
    have hlog16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, log_pow]
      push_cast
      ring
    rw [hlog16] at h16
    linarith
  linarith

/-! ### The hypothesis of the printed lemma at `a = 1`, `lambda = 1` -/

/-- The function `a(n) = 1` satisfies the hypothesis of the printed Lemma 2.8 with
`λ = 1` and constant `2`, for `x ≥ 3`: `sum_{n <= x} |1|^2/n = H_{floor x} ≤ 1 + log x ≤ 2 log x`. -/
theorem one_hypothesis_wu_lemma28 (x : ℝ) (hx : 3 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, |(1 : ℝ)| ^ 2 / n ≤ 2 * log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : ∑ n ∈ Icc 1 ⌊x⌋₊, |(1 : ℝ)| ^ 2 / n = ∑ n ∈ Icc 1 ⌊x⌋₊, ((n : ℝ))⁻¹ := by
    refine sum_congr rfl (fun n _ => ?_)
    rw [abs_one, one_pow, one_div]
  rw [h1, sum_inv_Icc_eq_harmonic]
  have hle := harmonic_le_one_add_log ⌊x⌋₊
  have hfloor : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x := by
    refine log_le_log ?_ (Nat.floor_le hx0.le)
    exact_mod_cast Nat.floor_pos.mpr (by linarith)
  have hone : (1 : ℝ) ≤ Real.log x := by
    have hexp : Real.exp 1 < x := lt_of_lt_of_le Real.exp_one_lt_d9 (by linarith)
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at this
    exact this.le
  linarith

/-! ### The refutation -/

/-- Wu 1993, Lemme 2.8, page 116, is FALSE as printed. With `a_1 = a_2 = 1` and
`λ_1 = λ_2 = 1` (hypothesis checked in `one_hypothesis_wu_lemma28`) the convolution
`a_1 * a_2` is the divisor function `tau(n) = (n.divisors).card`, and the conclusion of
the printed lemma, `sum_{n <= x} tau(n)^2/n ≪ L^2`, fails: no constant `K` bounds
`sum_{n <= x} tau(n)^2/n` by `K * (log x)^2` for all large `x`, since the sum is of
order `L^3`. -/
theorem not_wu_lemma28_printed :
    ¬ ∃ K : ℝ, ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
      ∑ n ∈ Icc 1 ⌊x⌋₊, ((n.divisors.card : ℕ) : ℝ) ^ 2 / n ≤ K * log x ^ 2 := by
  rintro ⟨K, x0, hK⟩
  -- pick a natural number `N` past `x0`, past `16`, and with `log N` past `4096 |K| + 64`
  obtain ⟨N, hNx0, hN16, hNlog⟩ : ∃ N : ℕ, x0 ≤ N ∧ (16 : ℝ) ≤ N ∧
      4096 * |K| + 64 ≤ log N := by
    set C : ℝ := max (max x0 16) (Real.exp (4096 * |K| + 64)) with hC
    obtain ⟨n, hn⟩ := exists_nat_gt C
    have h1 : x0 ≤ C := le_trans (le_max_left x0 16) (le_max_left (max x0 16) _)
    have h2 : (16 : ℝ) ≤ C := le_trans (le_max_right x0 16) (le_max_left (max x0 16) _)
    have h3 : Real.exp (4096 * |K| + 64) ≤ C := le_max_right (max x0 16) _
    refine ⟨n, by linarith, by linarith, ?_⟩
    have hexp : Real.exp (4096 * |K| + 64) < (n : ℝ) := lt_of_le_of_lt h3 hn
    have hlt := Real.log_lt_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at hlt
    exact hlt.le
  have hNm : (0 : ℝ) < N := by linarith
  have hL1 : (1 : ℝ) ≤ log N := by
    have : Real.log 16 ≤ log N := log_le_log (by norm_num) hN16
    have hlog16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, log_pow]
      push_cast
      ring
    have h2 : (0.5 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans_le' (by norm_num)
    rw [hlog16] at this
    linarith
  -- the two bounds on `sum tau(n)^2/n` at `x = N`
  set M : ℕ := ⌊Real.sqrt (N : ℝ)⌋₊ with hM
  have hMM : M * M ≤ N := by
    have h1 : ((M : ℝ)) ≤ Real.sqrt (N : ℝ) := Nat.floor_le (by positivity)
    have h2 : ((M : ℝ)) * M ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
      mul_self_le_mul_self (by positivity) h1
    have h3 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N :=
      Real.mul_self_sqrt hNm.le
    have : ((M * M : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      rw [h3] at h2
      exact h2
    exact_mod_cast this
  have hN16n : 16 ≤ N := by exact_mod_cast hN16
  have hquarter := quarter_log_le_harmonic_sqrt N hN16n
  have hH0 : 0 ≤ ∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹ := by positivity
  have hcs := tau_sq_div_sum_ge N M (by omega) hMM
  have hupper := hK (N : ℝ) hNx0
  rw [Nat.floor_natCast] at hupper
  -- combine: L^3/4096 ≤ K L^2
  have hL3 : log N ^ 3 / 4096 ≤ K * log N ^ 2 := by
    have h1 : log N / 4 ≤ ∑ d ∈ Icc 1 M, ((d : ℝ))⁻¹ := hquarter
    have h2 : (log N / 4) ^ 4 / (1 + log N) ≤
        ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 2 / n :=
      le_trans (by
        refine div_le_div_of_nonneg_right ?_ (by linarith)
        exact pow_le_pow_left₀ (by linarith) h1 4) hcs
    have h3 : log N ^ 3 / 4096 ≤ (log N / 4) ^ 4 / (1 + log N) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith [hL1, sq_nonneg (log N), pow_pos (show (0:ℝ) < log N by linarith) 3]
    linarith
  have hLpos : 0 < log N := by linarith
  have hL2 : 0 < log N ^ 2 := by positivity
  have hmul : log N * log N ^ 2 ≤ (4096 * K) * log N ^ 2 := by
    have h4 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4096)).mp hL3
    nlinarith [h4]
  have hKge : log N ≤ 4096 * K := le_of_mul_le_mul_right hmul hL2
  have hKpos : 0 < K := by nlinarith [hKge, hLpos]
  have hLge : 4096 * K + 64 ≤ log N := by
    rw [abs_of_pos hKpos] at hNlog
    exact hNlog
  linarith

end LeanLab.Cai2002
