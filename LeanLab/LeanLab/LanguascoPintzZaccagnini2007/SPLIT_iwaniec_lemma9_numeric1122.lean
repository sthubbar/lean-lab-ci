import Mathlib

/-!
A split of the MEDIUM leaf `iwaniec_lemma9_numeric1122` of
`SPLIT_iwaniec_lemma9_circles1122`: the closing numerical inequality of the proof of Lemma 9 on
page 102 of H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, 97 to 104,
`η⁻¹ ∏_{p ∣ d} (1 + p^(η-1)) (d^(100η) + exp (60 l^(1/4))) < M`, `M = (d^η exp l^(1/4))^100`.
The paper states it without proof. The steps here:
* `∏ (1 + p^(η-1)) ≤ exp ∑ p^(η-1)`, proved;
* `∑_{p ∣ q} p^(η-1) ≤ 5 + 2 log l`, proved;
* `η⁻¹ e⁵ l² (1 + exp (60 l^(1/4))) ≤ exp (100 l^(1/4))`, proved;
* the assembly with `d^(100η) ≥ 1`, in `SPLIT_iwaniec_lemma9_circles1122`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Real Finset


/-- Iwaniec 1974 page 102, proof of Lemma 9, first step of the numerical inequality:
`∏_{p ∣ q} (1 + p^(η-1)) ≤ exp (∑_{p ∣ q} p^(η-1))`, from `1 + x ≤ eˣ`. -/
theorem iwaniec_lemma9_euler_exp1122 (q : ℕ) (η : ℝ) :
    (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1))) ≤
      Real.exp (∑ p ∈ q.primeFactors, (p : ℝ) ^ (η - 1)) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
  have := Real.add_one_le_exp ((p : ℝ) ^ (η - 1))
  linarith

/-- Iwaniec 1974 page 102: for `q ≥ 3` the quantity `l = log (q (|γ| + 3))` exceeds `2`,
since `q (|γ| + 3) ≥ 9 > e²`. -/
theorem iwaniec_l_gt_two1122 (q : ℕ) (hq : 3 ≤ q) (γ l : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3))) : 2 < l := by
  rw [hl]
  have h9 : (9 : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by
    have : (3:ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [abs_nonneg γ]
  have : (2:ℝ) < Real.log 9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]; nlinarith [Real.exp_pos 1]
  linarith [Real.log_le_log (by norm_num) h9]

/-- Iwaniec 1974 page 102, proof of Lemma 9, the bound for `∏_{p ∣ d} (1 + p^(η-1))`
through its logarithm: `∑_{p ∣ q} p^(η-1) ≤ 5 + 2 log l`.
Proof: split at `p ≤ l`. Small primes give at most `l^η ∑_{n ≤ l} 1/n ≤ l^η (1 + log l)`;
the primes `p > l` dividing `q` number fewer than `log q / log l ≤ l / log l` and each gives at most
`l^(η-1)`, so together at most `2 / log l`. Finally `log l ≤ 2 √l / e` and
`log (2l)^(3/4) ≥ 1.09` give `η log l ≤ log 2`, so `l^η ≤ 2`, and
`2 (1 + log l) + 2 / log 2 < 5 + 2 log l`. A floating point scan of `η log l` over
`l ≥ log 9` gives the maximum `0.4096`. -/
theorem iwaniec_lemma9_primesum1122 (q : ℕ) (hq : 3 ≤ q) (γ l η : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹) :
    ∑ p ∈ q.primeFactors, (p : ℝ) ^ (η - 1) ≤ 5 + 2 * Real.log l := by
  have hl2 := iwaniec_l_gt_two1122 q hq γ l hl
  have hl0 : 0 < l := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have he := Real.exp_one_gt_d9
  -- bound on η log l
  have hsq : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl0
  have hb1 : 1.2 ≤ Real.log (2 * l) := by
    have : Real.log 4 ≤ Real.log (2 * l) := Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hb2 : 1.09 ≤ Real.log (2 * l) ^ (3 / 4 : ℝ) := by
    have h1 : Real.log (2 * l) ^ (1 / 2 : ℝ) ≤ Real.log (2 * l) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 : 1.09 ≤ Real.sqrt (Real.log (2 * l)) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    linarith
  have hlogl : Real.log l ≤ 2 * Real.sqrt l / Real.exp 1 := by
    have h1 : Real.log l = 2 * Real.log (Real.sqrt l) := by
      rw [Real.log_sqrt hl0.le]; ring
    have h2 := Real.log_le_sub_one_of_pos (div_pos hsq (Real.exp_pos 1))
    rw [Real.log_div hsq.ne' (Real.exp_pos 1).ne', Real.log_exp] at h2
    have h3 : 2 * Real.sqrt l / Real.exp 1 = 2 * (Real.sqrt l / Real.exp 1) := by ring
    linarith
  have hηl : η * Real.log l ≤ Real.log 2 := by
    rw [hη, inv_mul_le_iff₀ (by positivity)]
    have h3 : 2 * Real.sqrt l / Real.exp 1 ≤ 0.74 * Real.sqrt l := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
    have hp : 0.75 ≤ Real.log (2 * l) ^ (3 / 4 : ℝ) * Real.log 2 := by nlinarith
    have hp2 : Real.sqrt l * 0.75 ≤ Real.sqrt l * (Real.log (2 * l) ^ (3 / 4 : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hp hsq.le
    have hp3 : Real.sqrt l * (Real.log (2 * l) ^ (3 / 4 : ℝ) * Real.log 2) =
        Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ) * Real.log 2 := by ring
    linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  have hlη : l ^ η ≤ 2 := by
    rw [Real.rpow_def_of_pos hl0, mul_comm]
    calc Real.exp (η * Real.log l) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hηl
      _ = 2 := Real.exp_log (by norm_num)
  -- split the sum
  rw [← Finset.sum_filter_add_sum_filter_not q.primeFactors (fun p : ℕ => (p : ℝ) ≤ l)]
  -- small primes
  have hsmall : ∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ l), (p : ℝ) ^ (η - 1)
      ≤ 2 + 2 * Real.log l := by
    calc ∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ l), (p : ℝ) ^ (η - 1)
        ≤ ∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ l), 2 * (1 / (p : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_filter] at hp
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).one_lt.le
          have hp0 : (0 : ℝ) < p := by linarith
          rw [Real.rpow_sub hp0, Real.rpow_one]
          have : (p : ℝ) ^ η ≤ 2 := (Real.rpow_le_rpow hp0.le hp.2 hηpos.le).trans hlη
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 * ∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ l), (1 / (p : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * ∑ n ∈ Finset.Icc 1 ⌊l⌋₊, (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_Icc]
            exact ⟨(Nat.prime_of_mem_primeFactors hp.1).one_lt.le, Nat.le_floor hp.2⟩
          · intro n _ _; positivity
      _ ≤ 2 * (1 + Real.log l) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have hh := harmonic_le_one_add_log ⌊l⌋₊
          rw [harmonic_eq_sum_Icc] at hh
          push_cast at hh
          have hf : Real.log (⌊l⌋₊ : ℝ) ≤ Real.log l := by
            have : (0:ℝ) < ⌊l⌋₊ := by
              have : 1 ≤ ⌊l⌋₊ := Nat.le_floor (by norm_num; linarith)
              exact_mod_cast this
            exact Real.log_le_log this (Nat.floor_le hl0.le)
          simp only [one_div] at hh ⊢
          linarith
      _ = 2 + 2 * Real.log l := by ring
  -- large primes
  have hlarge : ∑ p ∈ q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ l), (p : ℝ) ^ (η - 1)
      ≤ 2.9 := by
    set B := q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ l)
    have hterm : ∀ p ∈ B, (p : ℝ) ^ (η - 1) ≤ 2 / l := by
      intro p hp
      rw [Finset.mem_filter, not_le] at hp
      have : (p : ℝ) ^ (η - 1) ≤ l ^ (η - 1) :=
        Real.rpow_le_rpow_of_nonpos hl0 hp.2.le (by
          have : η ≤ 1 := by nlinarith [Real.log_le_log (by norm_num) hl2.le]
          linarith)
      rw [Real.rpow_sub hl0, Real.rpow_one] at this
      calc (p : ℝ) ^ (η - 1) ≤ l ^ η / l := this
        _ ≤ 2 / l := div_le_div_of_nonneg_right hlη hl0.le
    have hcard : (B.card : ℝ) * Real.log l ≤ l := by
      have hdvd : ∏ p ∈ B, p ∣ q :=
        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
          (Nat.prod_primeFactors_dvd q)
      have hq0 : 0 < q := by omega
      have hle : (∏ p ∈ B, (p : ℝ)) ≤ q := by
        have := Nat.le_of_dvd hq0 hdvd
        rw [← Nat.cast_prod]; exact_mod_cast this
      have hpow : l ^ B.card ≤ ∏ p ∈ B, (p : ℝ) := by
        rw [← Finset.prod_const]
        apply Finset.prod_le_prod₀ (fun _ _ => hl0.le)
        intro p hp
        rw [Finset.mem_filter, not_le] at hp
        exact hp.2.le
      have h1 : (B.card : ℝ) * Real.log l = Real.log (l ^ B.card) := by
        rw [Real.log_pow]
      have hq1 : (q : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by
        have : (0:ℝ) ≤ q := by positivity
        nlinarith [abs_nonneg γ]
      rw [h1]
      calc Real.log (l ^ B.card) ≤ Real.log ((q : ℝ) * (|γ| + 3)) :=
            Real.log_le_log (pow_pos hl0 _) (by linarith)
        _ = l := hl.symm
    calc ∑ p ∈ B, (p : ℝ) ^ (η - 1) ≤ ∑ p ∈ B, 2 / l := Finset.sum_le_sum hterm
      _ = (B.card : ℝ) * (2 / l) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2.9 := by
        have hll : 0.69 < Real.log l := by
          linarith [Real.log_lt_log (by norm_num) hl2]
        rw [mul_div_assoc', div_le_iff₀ hl0]
        nlinarith
  linarith

/-- Iwaniec 1974 page 102, proof of Lemma 9, last step of the numerical inequality:
`η⁻¹ e⁵ l² (1 + exp (60 l^(1/4))) ≤ exp (100 l^(1/4))`, using `η⁻¹ ≤ 2 l²`,
`log l ≤ 4 l^(1/4)` and `l^(1/4) ≥ 1`. -/
theorem iwaniec_lemma9_final1122 (q : ℕ) (hq : 3 ≤ q) (γ l η : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹) :
    η⁻¹ * Real.exp (5 + 2 * Real.log l) * (1 + Real.exp (60 * l ^ (1 / 4 : ℝ))) ≤
      Real.exp (100 * l ^ (1 / 4 : ℝ)) := by
  have hl2 := iwaniec_l_gt_two1122 q hq γ l hl
  have hl0 : 0 < l := by linarith
  set L := l ^ (1 / 4 : ℝ) with hL
  have hL1 : 1 ≤ L := Real.one_le_rpow (by linarith) (by norm_num)
  have hlogL : Real.log l ≤ 4 * L := by
    have h1 : Real.log L = (1/4) * Real.log l := Real.log_rpow hl0 _
    have h2 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < L)
    linarith
  have hinv : η⁻¹ ≤ 2 * l ^ 2 := by
    rw [hη, inv_inv]
    have hs : Real.sqrt l ≤ l := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hlog1 : 1 ≤ Real.log (2 * l) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hpow : Real.log (2 * l) ^ (3 / 4 : ℝ) ≤ Real.log (2 * l) := by
      conv_rhs => rw [← Real.rpow_one (Real.log (2 * l))]
      exact Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have hlog2 : Real.log (2 * l) ≤ 2 * l := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 2 * l); linarith
    have h0 : 0 ≤ Real.log (2 * l) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ) ≤ l * (2 * l) :=
          mul_le_mul hs (hpow.trans hlog2) h0 (by linarith)
      _ = 2 * l ^ 2 := by ring
  have hexp2 : Real.exp (5 + 2 * Real.log l) = Real.exp 5 * l ^ 2 := by
    rw [Real.exp_add, show 2 * Real.log l = ((2:ℕ):ℝ) * Real.log l by norm_num,
      Real.exp_nat_mul, Real.exp_log hl0]
  have hl4 : 2 * l ^ 2 * (Real.exp 5 * l ^ 2) = Real.exp (Real.log 2 + 5 + 4 * Real.log l) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
      show 4 * Real.log l = ((4:ℕ):ℝ) * Real.log l by norm_num, Real.exp_nat_mul,
      Real.exp_log hl0]; ring
  have hE : 1 + Real.exp (60 * L) ≤ Real.exp (Real.log 2 + 60 * L) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
    have : 1 ≤ Real.exp (60 * L) := Real.one_le_exp (by linarith)
    linarith
  have hlog2 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; have := Real.exp_one_gt_d9; linarith
  calc η⁻¹ * Real.exp (5 + 2 * Real.log l) * (1 + Real.exp (60 * L))
      ≤ (2 * l ^ 2 * (Real.exp 5 * l ^ 2)) * Real.exp (Real.log 2 + 60 * L) := by
        rw [hexp2]
        apply mul_le_mul _ hE (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = Real.exp (Real.log 2 + 5 + 4 * Real.log l + (Real.log 2 + 60 * L)) := by
        rw [hl4, ← Real.exp_add]
    _ ≤ Real.exp (100 * L) := by
        apply Real.exp_le_exp.mpr
        nlinarith

end LeanLab.LPZ2007
