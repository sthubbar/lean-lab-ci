import LeanLab.Halupczok2012.Feed1122SawtoothSumBound

/-!
S136 deepening of the HARD leaf `tail_sawtooth_bound` of Feed1122SawtoothSumBound.
Halupczok journal page 337 cites the Voronoi divisor bound. The classical proof, as in
Titchmarsh, The theory of the Riemann zeta function, 2nd ed., section 12.2 with Theorem 5.9,
and Graham and Kolesnik, Van der Corput's method of exponential sums, chapter 4, cuts the
range x to one third below m at most root x into dyadic blocks a below m at most b with
b at most 2a. Each block is O of x to one third by the second derivative test applied to the
sawtooth of x over m, whose second derivative is of size x over a cubed; and there are
O of log x blocks. The dyadic decomposition, the block counting and the reduction of each block to the
second derivative test are proved here; the second derivative test for sawtooth sums is the
remaining HARD leaf.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122SawtoothSumBoundS136Dyadic

open Finset

/-- LEAF: second derivative test for sawtooth sums, the step used per dyadic block in the
classical proof of the Voronoi bound cited on Halupczok page 337: Titchmarsh, The theory of the
Riemann zeta function, section 12.2 with Theorem 5.9, and Graham and Kolesnik, Van der Corput's
method of exponential sums, the second derivative test of chapter 2 combined with Vaaler's
trigonometric approximation of the sawtooth. If f is twice differentiable on a to b with
lam at most f'' at most 8 lam, then the sum over a below m at most b of fract of f m minus one
half is O of b minus a times lam to one third plus lam to minus one half, with an absolute
constant. Class HARD: a genuine exponential sum estimate, a printed textbook theorem. -/
theorem psi_second_derivative_test :
    ∃ C : ℝ, 0 < C ∧ ∀ (f f' f'' : ℝ → ℝ) (lam : ℝ) (a b : ℕ), 0 < lam →
      a ≤ b → (∀ t ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f' t) t ∧ HasDerivAt f' (f'' t) t ∧
        lam ≤ f'' t ∧ f'' t ≤ 8 * lam) →
      |∑ m ∈ Ioc a b, (Int.fract (f m) - 1 / 2)| ≤
        C * (((b : ℝ) - a) * lam ^ (1 / 3 : ℝ) + lam ^ (-(1 / 2) : ℝ)) := by
  sorry

/-- Per dyadic block bound: for a block a below m at most b with floor of x to one third at most
a, b at most 2a and b at most root x, the sawtooth sum of x over m is at most 3C times x to one
third. Proved from the leaf with f of t equal to x over t, f'' of t equal to 2x over t cubed and
lam equal to x over 4 a cubed: a times lam to one third is x over 4 to one third, and
lam to minus one half is at most 2 x to one third since a squared is at most x. -/
theorem block_sawtooth_bound :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x → ∀ a b : ℕ,
      ⌊x ^ (1 / 3 : ℝ)⌋₊ ≤ a → b ≤ 2 * a → b ≤ ⌊Real.sqrt x⌋₊ →
        |∑ m ∈ Ioc a b, (Int.fract (x / m) - 1 / 2)| ≤ C * x ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hT⟩ := psi_second_derivative_test
  refine ⟨3 * C, 1, by positivity, fun x hx a b ha hb hbN => ?_⟩
  rcases le_or_gt b a with hab | hab
  · have : Ioc a b = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [this, sum_empty, abs_zero]; positivity
  have ha1 : 1 ≤ a := by omega
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha1
  have hx0 : 0 < x := by linarith
  set lam : ℝ := x / (4 * (a : ℝ) ^ 3) with hlam
  have hlampos : 0 < lam := by positivity
  have hderiv : ∀ t ∈ Set.Icc (a : ℝ) b,
      HasDerivAt (fun t => x / t) (-x * (t ^ 2)⁻¹) t ∧
      HasDerivAt (fun t => -x * (t ^ 2)⁻¹) (2 * x / t ^ 3) t ∧
      lam ≤ 2 * x / t ^ 3 ∧ 2 * x / t ^ 3 ≤ 8 * lam := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hapos ht.1
    have htb : t ≤ 2 * a := ht.2.trans (by exact_mod_cast hb)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := (hasDerivAt_inv ht0.ne').const_mul x
      convert h using 1
      · ext s; simp [div_eq_mul_inv]
      · ring
    · have h := ((hasDerivAt_pow 2 t).inv (by positivity)).const_mul (-x)
      convert h using 1
      field_simp
      ring
    · rw [hlam, div_le_div_iff₀ (by positivity) (by positivity)]
      have : t ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ ht0.le htb 3
      nlinarith
    · rw [hlam, div_le_iff₀ (by positivity)]
      have : (a : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hapos.le ht.1 3
      field_simp
      nlinarith
  have hmain := hT (fun t => x / t) (fun t => -x * (t ^ 2)⁻¹) (fun t => 2 * x / t ^ 3) lam a b
    hlampos hab.le hderiv
  -- first term
  have hba : ((b : ℝ) - a) ≤ a := by
    have : (b : ℝ) ≤ 2 * a := by exact_mod_cast hb
    linarith
  have h1 : (a : ℝ) * lam ^ (1 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
    have e : (a : ℝ) * lam ^ (1 / 3 : ℝ) = (x / 4) ^ (1 / 3 : ℝ) := by
      have : (a : ℝ) = ((a : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hapos.le]; norm_num
      rw [this, ← Real.mul_rpow (by positivity) hlampos.le, hlam]
      congr 1
      field_simp
    rw [e]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hfirst : ((b : ℝ) - a) * lam ^ (1 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
    (mul_le_mul_of_nonneg_right hba (by positivity)).trans h1
  -- second term
  have hasq : (a : ℝ) ≤ Real.sqrt x := by
    have h1 : (a : ℝ) < b := by exact_mod_cast hab
    have h2 : (b : ℝ) ≤ Real.sqrt x :=
      (Nat.cast_le.mpr hbN).trans (Nat.floor_le (Real.sqrt_nonneg x))
    linarith
  have ha2 : (a : ℝ) ^ 2 ≤ x := by
    have := pow_le_pow_left₀ hapos.le hasq 2
    rwa [Real.sq_sqrt hx0.le] at this
  have hsecond : lam ^ (-(1 / 2) : ℝ) ≤ 2 * x ^ (1 / 3 : ℝ) := by
    have hinv : lam ^ (-(1 / 2) : ℝ) = (4 * (a : ℝ) ^ 3 / x) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg hlampos.le, ← Real.inv_rpow hlampos.le, hlam, inv_div]
    rw [hinv]
    have hle : 4 * (a : ℝ) ^ 3 / x ≤ (2 * x ^ (1 / 3 : ℝ)) ^ 2 := by
      rw [div_le_iff₀ hx0]
      have hx13 : 1 ≤ x ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have hcube : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      -- a^3 ≤ x * a ≤ x * sqrt x ≤ x * x^(2/3)?  use a^6 ≤ x^3 ≤ x^4 ... via squares
      have ha6 : ((a : ℝ) ^ 3) ^ 2 ≤ (x * (x ^ (1 / 3 : ℝ)) ^ 2) ^ 2 := by
        have : ((a : ℝ) ^ 3) ^ 2 = ((a : ℝ) ^ 2) ^ 3 := by ring
        rw [this]
        have h3 : ((a : ℝ) ^ 2) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by positivity) ha2 3
        have : x ^ 3 ≤ (x * (x ^ (1 / 3 : ℝ)) ^ 2) ^ 2 := by
          have : (x * (x ^ (1 / 3 : ℝ)) ^ 2) ^ 2 = x ^ 3 * x ^ (1 / 3 : ℝ) := by
            calc (x * (x ^ (1 / 3 : ℝ)) ^ 2) ^ 2 = x ^ 2 * ((x ^ (1 / 3 : ℝ)) ^ 3 * x ^ (1 / 3 : ℝ)) := by ring
              _ = _ := by rw [hcube]; ring
          rw [this]
          nlinarith [pow_pos hx0 3]
        linarith
      have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2:ℕ) ≠ 0)).mp ha6
      nlinarith
    calc (4 * (a : ℝ) ^ 3 / x) ^ (1 / 2 : ℝ) ≤ ((2 * x ^ (1 / 3 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = 2 * x ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  calc _ ≤ _ := hmain
    _ ≤ C * (x ^ (1 / 3 : ℝ) + 2 * x ^ (1 / 3 : ℝ)) := by gcongr
    _ = 3 * C * x ^ (1 / 3 : ℝ) := by ring

/-- Dyadic decomposition: if the block bound holds at level x, then a range a below m at most
N with N at most 2 to the k times a, a at least floor of x to one third, and a at least one,
splits into at most k dyadic blocks, so its sawtooth sum is at most k times the block bound. -/
theorem dyadic_sum_bound (x B : ℝ) (N : ℕ)
    (hblock : ∀ a b : ℕ, ⌊x ^ (1 / 3 : ℝ)⌋₊ ≤ a → b ≤ 2 * a → b ≤ N →
        |∑ m ∈ Ioc a b, (Int.fract (x / m) - 1 / 2)| ≤ B) (hB : 0 ≤ B) :
    ∀ k : ℕ, ∀ a : ℕ, ⌊x ^ (1 / 3 : ℝ)⌋₊ ≤ a → 1 ≤ a → N ≤ 2 ^ k * a →
      |∑ m ∈ Ioc a N, (Int.fract (x / m) - 1 / 2)| ≤ k * B := by
  intro k
  induction k with
  | zero =>
    intro a _ _ hN
    have : Ioc a N = ∅ := Finset.Ioc_eq_empty (by simp at hN; omega)
    simp [this]
  | succ k ih =>
    intro a ha0 ha1 hN
    by_cases h2 : N ≤ 2 * a
    · have := hblock a N ha0 h2 le_rfl
      push_cast
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · rw [not_le] at h2
      have hsplit : Ioc a N = Ioc a (2 * a) ∪ Ioc (2 * a) N :=
        (Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)).symm
      have hdisj : Disjoint (Ioc a (2 * a)) (Ioc (2 * a) N) :=
        Finset.Ioc_disjoint_Ioc_of_le le_rfl
      rw [hsplit, Finset.sum_union hdisj]
      have h1 := hblock a (2 * a) ha0 le_rfl h2.le
      have h3 := ih (2 * a) (by omega) (by omega) (by rw [pow_succ] at hN; linarith)
      push_cast
      calc
        _ ≤ _ := abs_add_le _ _
        _ ≤ B + k * B := add_le_add h1 h3
        _ = (k + 1) * B := by ring

/-- Counting the dyadic blocks: Nat.log 2 N is at most log x over log 2 when N is at most x and x is at least 1. -/
theorem natLog_le_log (x : ℝ) (N : ℕ) (hx : 1 ≤ x) (hN : (N : ℝ) ≤ x) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp only [Nat.log_zero_right, CharP.cast_eq_zero, zero_mul]
    exact Real.log_nonneg hx
  · have hp : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hpos.ne'
    have hp' : ((2 : ℝ) ^ Nat.log 2 N) ≤ x := by
      exact le_trans (by exact_mod_cast hp) hN
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hp'

/-- The tail sawtooth bound, assembled from the proved block bound by the proved dyadic decomposition
and block counting. Statement identical to `tail_sawtooth_bound`. -/
theorem tail_sawtooth_bound_of_leaves :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |∑ m ∈ (Icc 1 ⌊Real.sqrt x⌋₊).filter (fun m => ⌊x ^ (1 / 3 : ℝ)⌋₊ < m),
          (Int.fract (x / m) - 1 / 2)| ≤
        C * x ^ (1 / 3 : ℝ) * Real.log x := by
  obtain ⟨C, X0, hC, hT⟩ := block_sawtooth_bound
  refine ⟨3 * C, max X0 3, by positivity, fun x hx => ?_⟩
  have hx3 : (3 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      ((Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx3)
  set a0 := ⌊x ^ (1 / 3 : ℝ)⌋₊ with ha0def
  set N := ⌊Real.sqrt x⌋₊ with hNdef
  have hp : 0 ≤ x ^ (1 / 3 : ℝ) := by positivity
  have ha1 : 1 ≤ a0 := by
    rw [ha0def, Nat.one_le_floor_iff]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hfilt : (Icc 1 N).filter (fun m => a0 < m) = Ioc a0 N := by
    ext m
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [hfilt]
  set k := Nat.log 2 N + 1 with hk
  have hNk : N ≤ 2 ^ k * a0 := by
    have := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le
    calc N ≤ 2 ^ k := this
      _ = 2 ^ k * 1 := by ring
      _ ≤ 2 ^ k * a0 := Nat.mul_le_mul_left _ ha1
  have hB : 0 ≤ C * x ^ (1 / 3 : ℝ) := by positivity
  have hD := dyadic_sum_bound x (C * x ^ (1 / 3 : ℝ)) N
    (fun a b h1 h2 h3 => hT x ((le_max_left _ _).trans hx) a b h1 h2 h3) hB k a0 le_rfl ha1 hNk
  have hNx : (N : ℝ) ≤ x := by
    have h1 : (N : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
    have h2 : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  have hL := natLog_le_log x N (by linarith) hNx
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hkle : (k : ℝ) ≤ 3 * Real.log x := by
    rw [hk]
    push_cast
    have : (Nat.log 2 N : ℝ) ≤ 2 * Real.log x := by
      nlinarith [(Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ _)]
    linarith
  calc
    _ ≤ (k : ℝ) * (C * x ^ (1 / 3 : ℝ)) := hD
    _ ≤ (3 * Real.log x) * (C * x ^ (1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hkle hB
    _ = 3 * C * x ^ (1 / 3 : ℝ) * Real.log x := by ring

end LeanLab.Halupczok2012.Feed1122SawtoothSumBoundS136Dyadic

#print axioms LeanLab.Halupczok2012.Feed1122SawtoothSumBoundS136Dyadic.block_sawtooth_bound
#print axioms LeanLab.Halupczok2012.Feed1122SawtoothSumBoundS136Dyadic.dyadic_sum_bound
#print axioms LeanLab.Halupczok2012.Feed1122SawtoothSumBoundS136Dyadic.natLog_le_log
#print axioms LeanLab.Halupczok2012.Feed1122SawtoothSumBoundS136Dyadic.tail_sawtooth_bound_of_leaves
