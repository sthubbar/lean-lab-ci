import LeanLab.Akeno2026.Statements
import LeanLab.PNTPort.BV.Helpers

namespace LeanLab.Akeno2026.DecompJ267

open LeanLab.Akeno2026
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-- Page 7 Theorem 3.1. The one factor beta sum is truncated von Mangoldt. -/
theorem beta_one_truncated221 (X : ℝ) (n : ℕ) : beta 1 (fun _ => 1) (fun _ => X) n =
    if n ∈ Finset.Ioc 1 ⌊X⌋₊ then Λ n else 0 := by
  classical
  have hs : ((Fintype.piFinset fun _ : Fin 1 => Finset.Ioc 1 ⌊X⌋₊).filter
      (fun v => ∏ i, v i = n)) =
      if n ∈ Finset.Ioc 1 ⌊X⌋₊ then {fun _ => n} else ∅ := by
    ext v
    simp only [mem_filter, Fintype.mem_piFinset, Fin.forall_fin_one,
      Fin.prod_univ_one]
    split_ifs with hn
    · simp only [mem_singleton]
      constructor
      · intro h
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa [hi] using h.2
      · intro h
        subst v
        exact ⟨hn, rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro hv he
      exact hn (he ▸ hv)
  unfold beta
  simp only [Nat.floor_one]
  rw [hs]
  split_ifs <;> simp

/-- Page 7 Theorem 3.1. Exact additive split of one factor interval. -/
theorem beta_interval_split221 (k : ℕ) (j : Fin k) (lo hi : Fin k → ℝ) (T : ℝ) (n : ℕ)
    (hlo : lo j ≤ T) (hhi : T ≤ hi j) :
    beta k lo hi n =
      beta k lo (Function.update hi j T) n +
      beta k (Function.update lo j T) hi n := by
  classical
  have hL := Nat.floor_mono hlo
  have hH := Nat.floor_mono hhi
  let s := (Fintype.piFinset fun i => Finset.Ioc ⌊lo i⌋₊ ⌊hi i⌋₊).filter
    (fun v => ∏ i, v i = n)
  have hs1 : s.filter (fun v => v j ≤ ⌊T⌋₊) =
      (Fintype.piFinset fun i => Finset.Ioc ⌊lo i⌋₊ ⌊Function.update hi j T i⌋₊).filter
        (fun v => ∏ i, v i = n) := by
    ext v
    simp only [s, mem_filter, Fintype.mem_piFinset, mem_Ioc]
    constructor
    · rintro ⟨⟨hv, hp⟩, hj⟩
      refine ⟨fun i => ?_, hp⟩
      by_cases hij : i = j
      · subst i
        simpa using And.intro (hv j).1 hj
      · simpa [Function.update_of_ne hij] using hv i
    · rintro ⟨hv, hp⟩
      have hj : v j ≤ ⌊T⌋₊ := by simpa using (hv j).2
      refine ⟨⟨fun i => ?_, hp⟩, hj⟩
      by_cases hij : i = j
      · subst i
        exact ⟨(hv j).1, hj.trans hH⟩
      · simpa [Function.update_of_ne hij] using hv i
  have hs2 : s.filter (fun v => ¬ v j ≤ ⌊T⌋₊) =
      (Fintype.piFinset fun i => Finset.Ioc ⌊Function.update lo j T i⌋₊ ⌊hi i⌋₊).filter
        (fun v => ∏ i, v i = n) := by
    ext v
    simp only [s, mem_filter, Fintype.mem_piFinset, mem_Ioc, not_le]
    constructor
    · rintro ⟨⟨hv, hp⟩, hj⟩
      refine ⟨fun i => ?_, hp⟩
      by_cases hij : i = j
      · subst i
        simpa using And.intro hj (hv j).2
      · simpa [Function.update_of_ne hij] using hv i
    · rintro ⟨hv, hp⟩
      have hj : ⌊T⌋₊ < v j := by simpa using (hv j).1
      refine ⟨⟨fun i => ?_, hp⟩, hj⟩
      by_cases hij : i = j
      · subst i
        exact ⟨hL.trans_lt hj, (hv j).2⟩
      · simpa [Function.update_of_ne hij] using hv i
  simpa only [hs1, hs2, beta, s] using
    (Finset.sum_filter_add_sum_filter_not s (fun v => v j ≤ ⌊T⌋₊) (fun v => ∏ i, Λ (v i))).symm

/-- Page 7 Theorem 3.1. The beta cutoff loses no Mangoldt value below X. -/
theorem beta_one_eq221 (X : ℝ) (n : ℕ) (hn : n ≤ ⌊X⌋₊) :
    beta 1 (fun _ => 1) (fun _ => X) n = Λ n := by
  rw [beta_one_truncated221]
  by_cases h : 1 < n
  · rw [ite_eq_left (Finset.mem_Ioc.mpr ⟨h, hn⟩)]
  · have hn1 : n = 0 ∨ n = 1 := by omega
    rcases hn1 with rfl | rfl <;> simp

/-- Page 7 Theorem 3.1. The one factor beta error sum is the Lambda error sum. -/
theorem betaSum_one_eq221 (θ X : ℝ) (N : ℕ) (w₁ w₂ : ℝ → ℝ) (hN : N ≤ ⌊X⌋₊) :
    betaSum θ (beta 1 (fun _ => 1) (fun _ => X)) w₁ w₂ X N =
      betaSum θ (fun n => Λ n) w₁ w₂ X N := by
  have hfun : ∀ m : ℕ, beta 1 (fun _ => 1) (fun _ => X) (N - m) = Λ (N - m) :=
    fun m => beta_one_eq221 X (N - m) ((Nat.sub_le _ _).trans hN)
  simp only [betaSum, hfun]

/-- Page 7 proof of Theorem 1.1. Exact weighted finite Cauchy Schwarz bound. -/
theorem finite_weighted_square221 {ι : Type*} (s : Finset ι) (a R B : ι → ℝ)
    (hR : ∀ i ∈ s, 0 ≤ R i) (hB : ∀ i ∈ s, R i ≤ B i) :
    (∑ i ∈ s, a i * R i) ^ 2 ≤
      (∑ i ∈ s, a i ^ 2 * B i) * ∑ i ∈ s, R i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    exact mul_nonneg (sq_nonneg _) ((hR i hi).trans (hB i hi))
  · exact hR
  · intro i hi
    have h := mul_le_mul_of_nonneg_left (hB i hi) (mul_nonneg (sq_nonneg (a i)) (hR i hi))
    nlinarith only [h]

/-- Page 7 proof of Theorem 1.1. Moment bound with an explicit pointwise constant.
CONDITIONAL ON the supplied pointwise error bound. -/
theorem levelSum_square_cauchy221 (θ X : ℝ) (k N : ℕ) (w₁ w₂ : ℝ → ℝ) (C : ℝ)
    (_hX : 2 ≤ X) (_hC : 0 ≤ C)
    (hR : ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
      (supR w₁ w₂ X N d : ℝ) ≤ C * X / d * Real.log X ^ 2) :
    levelSum θ k w₁ w₂ X N ^ 2 ≤
      (C * X * Real.log X ^ 2 *
        ∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, (d.divisors.card : ℝ) ^ (2 * k) / d) *
          levelSum θ 0 w₁ w₂ X N := by
  have hc := finite_weighted_square221 (Finset.Icc 1 ⌊X ^ θ⌋₊)
    (fun d => (d.divisors.card : ℝ) ^ k) (fun d => (supR w₁ w₂ X N d : ℝ))
    (fun d => C * X / d * Real.log X ^ 2) (fun d hd => NNReal.coe_nonneg _) hR
  simp only [levelSum, pow_zero, one_mul]
  refine hc.trans_eq ?_
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← pow_mul]
  have he : k * 2 = 2 * k := Nat.mul_comm _ _
  rw [he]
  ring

/-- Page 7 proof of Theorem 1.1. Exact difference of the two main terms. -/
theorem Rdl_beta_decomposition221 (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ) :
    Rdl w₁ w₂ X N d l =
      ((∑ m ∈ Finset.range (N + 1),
        if (m : ℤ) ≡ l [ZMOD d] then
          Λ m * Λ (N - m) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X) else 0)
      - singSeries N / psiN N d *
        ∑ m ∈ Finset.range (N + 1),
          Λ (N - m) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X))
      + singSeries N / psiN N d *
        ∑ m ∈ Finset.range (N + 1),
          (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X) := by
  unfold Rdl
  simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

/-- Page 7 Theorem 3.1 specialized to one Mangoldt factor.
CONDITIONAL ON BetaLevel at theta and eta. -/
theorem betaLevel_lambda221 (θ η : ℝ) (hbeta : BetaLevel θ η) (w₁ w₂ : ℝ → ℝ)
    (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂) (A : ℝ) (hA : 0 < A) :
    ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X →
      (excCount (fun _ => True)
        (fun N => betaSum θ (fun n => Λ n) w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ)
          ≤ C₁ * X / Real.log X ^ A := by
  classical
  obtain ⟨C₁, C₂, hb⟩ := hbeta 1 (by omega) w₁ w₂ hw₁ hw₂ A hA
  refine ⟨C₁, C₂, fun X hX => ?_⟩
  have hadm : AdmissibleBeta η X 1 (fun _ => 1) (fun _ => X) := by
    exact Or.inl ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  have h := (hb X hX (fun _ => 1) (fun _ => X) hadm).1
  have he : excCount (fun _ => True)
      (fun N => betaSum θ (beta 1 (fun _ => 1) (fun _ => X)) w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X =
      excCount (fun _ => True)
      (fun N => betaSum θ (fun n => Λ n) w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X := by
    unfold excCount
    congr 1
    ext N
    by_cases hN : N ∈ Finset.Icc 1 ⌊X⌋₊
    · simp only [Finset.mem_filter, hN, true_and]
      rw [betaSum_one_eq221 θ X N w₁ w₂ (Finset.mem_Icc.mp hN).2]
    · simp only [Finset.mem_filter, hN, false_and]
  rwa [he] at h

/-- Page 7 proof of Theorem 1.1. Cauchy Schwarz with real half powers. -/
theorem finite_weighted_rpow221 {ι : Type*} (s : Finset ι) (a R B : ι → ℝ)
    (hR : ∀ i ∈ s, 0 ≤ R i)
    (hB : ∀ i ∈ s, R i ≤ B i) :
    (∑ i ∈ s, a i * R i) ≤
      (∑ i ∈ s, a i ^ 2 * B i) ^ ((1 : ℝ) / 2) *
        (∑ i ∈ s, R i) ^ ((1 : ℝ) / 2) := by
  have hc := finite_weighted_square221 s a R B hR hB
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i hi =>
    mul_nonneg (sq_nonneg _) ((hR i hi).trans (hB i hi))))]
  exact Real.le_sqrt_of_sq_le hc

/-- Page 7 proof of Theorem 1.1. Exact beta to zero moment comparison. -/
theorem levelSum_zero_le_beta221 (θ X : ℝ) (N : ℕ) (w₁ w₂ : ℝ → ℝ) :
    levelSum θ 0 w₁ w₂ X N ≤ betaSum θ (fun n => Λ n) w₁ w₂ X N +
      (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d|) *
        |∑ m ∈ Finset.range (N + 1),
          (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| := by
  classical
  let E := ∑ m ∈ Finset.range (N + 1),
    (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)
  let g := fun (d : ℕ) (l : ℕ) =>
    (∑ m ∈ Finset.range (N + 1), if (m : ℤ) ≡ l [ZMOD d] then
      Λ m * Λ (N - m) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X) else 0) -
    singSeries N / psiN N d * ∑ m ∈ Finset.range (N + 1),
      Λ (N - m) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)
  have heq : ∀ (d : ℕ) (l : ℕ), Rdl w₁ w₂ X N d l = g d l + singSeries N / psiN N d * E := by
    intro d l
    unfold Rdl g E
    simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
    ring
  let B : ℕ → ℝ := fun d =>
    ((((Finset.range d).filter (fun l : ℕ => Int.gcd d ((l : ℤ) * ((N : ℤ) - l)) = 1)).sup
      (fun l => ‖g d l‖₊) : NNReal) : ℝ)
  have hp : ∀ d : ℕ, (supR w₁ w₂ X N d : ℝ) ≤
      B d + |singSeries N / psiN N d| * |E| := by
    intro d
    let s := (Finset.range d).filter (fun l : ℕ => Int.gcd d ((l : ℤ) * ((N : ℤ) - l)) = 1)
    have hh : s.sup (fun l => ‖Rdl w₁ w₂ X N d l‖₊) ≤
        s.sup (fun l => ‖g d l‖₊) + ‖singSeries N / psiN N d * E‖₊ := by
      apply Finset.sup_le
      intro l hl
      rw [heq]
      exact (nnnorm_add_le _ _).trans
        (add_le_add (Finset.le_sup (f := fun l => ‖g d l‖₊) hl) le_rfl)
    have hh' := (show ((s.sup (fun l => ‖Rdl w₁ w₂ X N d l‖₊) : NNReal) : ℝ) ≤
        ((s.sup (fun l => ‖g d l‖₊) + ‖singSeries N / psiN N d * E‖₊ : NNReal) : ℝ) from by exact_mod_cast hh)
    simpa only [NNReal.coe_add, coe_nnnorm, norm_mul, Real.norm_eq_abs, supR, s, B] using hh'
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
        (B d + |singSeries N / psiN N d| * |E|) := by
      simp only [levelSum, pow_zero, one_mul]
      exact Finset.sum_le_sum (fun d hd => hp d)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      rfl

/-- Page 7 proof of Theorem 1.1. beta_empty_interval221. -/
theorem beta_empty_interval221 (k : ℕ) (j : Fin k) (lo hi : Fin k → ℝ) (n : ℕ)
    (h : hi j ≤ lo j) : beta k lo hi n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro v hv
  have hj := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hv).1) j
  have hm := Nat.floor_mono h
  have hb := Finset.mem_Ioc.mp hj
  omega

/-- Page 7 proof of Theorem 1.1. beta_interval_partition221. -/
theorem beta_interval_partition221 (k : ℕ) (j : Fin k) (lo hi : Fin k → ℝ) (cuts : ℕ → ℝ)
    (hcuts : Monotone cuts) (M n : ℕ) :
    beta k (Function.update lo j (cuts 0)) (Function.update hi j (cuts M)) n =
      ∑ r ∈ Finset.range M,
        beta k (Function.update lo j (cuts r)) (Function.update hi j (cuts (r + 1))) n := by
  classical
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact beta_empty_interval221 k j _ _ n (by simp)
  | succ M ih =>
    have hs := beta_interval_split221 k j (Function.update lo j (cuts 0))
      (Function.update hi j (cuts (M + 1))) (cuts M) n
      (by simpa using hcuts (Nat.zero_le M)) (by simpa using hcuts (Nat.le_succ M))
    simp only [Function.update_idem] at hs
    rw [hs, ih, Finset.sum_range_succ]

/-- Page 7 proof of Theorem 1.1. beta_dyadic_partition221. -/
theorem beta_dyadic_partition221 (k : ℕ) (j : Fin k) (lo hi : Fin k → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (M n : ℕ) :
    beta k (Function.update lo j L) (Function.update hi j (L * 2 ^ M)) n =
      ∑ r ∈ Finset.range M,
        beta k (Function.update lo j (L * 2 ^ r))
          (Function.update hi j (L * 2 ^ (r + 1))) n := by
  have hmono : Monotone (fun r : ℕ => L * (2 : ℝ) ^ r) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hab) hL
  simpa using beta_interval_partition221 k j lo hi (fun r => L * 2 ^ r) hmono M n

/-- Page 7 proof of Theorem 1.1. vonMangoldt_le_log_scale221. -/
theorem vonMangoldt_le_log_scale221 {X : ℝ} (hX : 2 ≤ X) {n : ℕ} (hn : (n : ℝ) ≤ X) :
    ‖Λ n‖ ≤ Real.log X := by
  rw [Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  by_cases hn0 : n = 0
  · subst n
    simpa using Real.log_nonneg (by linarith : 1 ≤ X)
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) hn)

/-- Page 7 proof of Theorem 1.1. Rdl_triangle_explicit221. -/
theorem Rdl_triangle_explicit221 (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ) (B : ℝ)
    (hX : 2 ≤ X) (hN : (N : ℝ) ≤ X) (hB : 0 ≤ B)
    (hW : ∀ m ∈ Finset.range (N + 1),
      |w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤ B) :
    ‖Rdl w₁ w₂ X N d l‖ ≤
      B * Real.log X ^ 2 *
        (((Finset.range (N + 1)).filter (fun m : ℕ => (m : ℤ) ≡ l [ZMOD d])).card : ℝ) +
      |singSeries N / psiN N d| * (B * (N + 1)) := by
  have hΛ : ∀ n : ℕ, (n : ℝ) ≤ X → ‖Λ n‖ ≤ Real.log X :=
    fun n hn => vonMangoldt_le_log_scale221 hX hn
  unfold Rdl
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [← Finset.sum_filter]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => (m : ℤ) ≡ l [ZMOD d]),
          B * Real.log X ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hmR := (Finset.mem_filter.mp hm).1
        have hmN : m ≤ N := by simpa using Finset.mem_range.mp hmR
        have hmX : (m : ℝ) ≤ X := (show (m : ℝ) ≤ N by exact_mod_cast hmN).trans hN
        have hnX : ((N - m : ℕ) : ℝ) ≤ X := (show ((N - m : ℕ) : ℝ) ≤ N by exact_mod_cast Nat.sub_le N m).trans hN
        calc
          _ = ‖Λ m‖ * ‖Λ (N - m)‖ *
              |w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| := by
                rw [show Λ m * Λ (N - m) * w₁ ((m : ℝ) / X) *
                    w₂ (((N - m : ℕ) : ℝ) / X) =
                    (Λ m * Λ (N - m)) * (w₁ ((m : ℝ) / X) *
                    w₂ (((N - m : ℕ) : ℝ) / X)) by ring]
                simp only [norm_mul, Real.norm_eq_abs, abs_mul]
          _ ≤ Real.log X * Real.log X * B := by
            exact mul_le_mul (mul_le_mul (hΛ m hmX) (hΛ (N - m) hnX)
              (norm_nonneg _) (Real.log_nonneg (by linarith : 1 ≤ X)))
              (hW m hmR) (abs_nonneg _) (mul_self_nonneg _)
          _ = B * Real.log X ^ 2 := by ring
      _ = _ := by simp [mul_comm]
  · rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ m ∈ Finset.range (N + 1), B := by
        apply Finset.sum_le_sum
        intro m hm
        simpa only [Real.norm_eq_abs] using hW m hm
      _ = _ := by simp [mul_comm]

/-- Page 7 proof of Theorem 1.1. residue_count_le221. -/
theorem residue_count_le221 (X : ℝ) (N d : ℕ) (l : ℤ) (hN : (N : ℝ) ≤ X)
    (hd : 1 ≤ d) (hdX : (d : ℝ) ≤ X) :
    (((Finset.range (N + 1)).filter (fun m : ℕ => (m : ℤ) ≡ l [ZMOD d])).card : ℝ) ≤
      2 * X / d := by
  classical
  have hc : ((Finset.range (N + 1)).filter
      (fun m : ℕ => (m : ℤ) ≡ l [ZMOD d])).card ≤ N / d + 1 := by
    have hcard : ((Finset.range (N + 1)).filter
        (fun m : ℕ => (m : ℤ) ≡ l [ZMOD d])).card ≤ (Finset.range (N / d + 1)).card := by
      apply Finset.card_le_card_of_injOn (f := fun m => m / d)
      · intro m hm
        have hmN : m ≤ N := by simpa using Finset.mem_range.mp (Finset.mem_filter.mp hm).1
        simpa using Nat.div_le_div_right hmN
      · intro m hm n hn he
        have hmod : m ≡ n [MOD d] := Int.natCast_modEq_iff.mp
          ((Finset.mem_filter.mp hm).2.trans (Finset.mem_filter.mp hn).2.symm)
        have hmdiv := Nat.mod_add_div m d
        have hndiv := Nat.mod_add_div n d
        change m % d = n % d at hmod
        change m / d = n / d at he
        calc
          m = m % d + d * (m / d) := hmdiv.symm
          _ = n % d + d * (n / d) := by rw [hmod, he]
          _ = n := hndiv
    simpa only [Finset.card_range] using hcard
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdiv : ((N / d : ℕ) : ℝ) ≤ X / d := by
    apply (le_div_iff₀ hdR).2
    have h := Nat.div_mul_le_self N d
    exact (show ((N / d : ℕ) : ℝ) * d ≤ N by exact_mod_cast h).trans hN
  have hXdiv : 1 ≤ X / d := (le_div_iff₀ hdR).2 (by simpa using hdX)
  calc
    _ ≤ ((N / d + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ X / d + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using (show ((N / d : ℕ) : ℝ) + 1 ≤ X / d + 1 by linarith)
    _ ≤ 2 * X / d := by rw [mul_div_assoc]; linarith

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. Rdl_pointwise_constant221. -/
theorem Rdl_pointwise_constant221 (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ) (B Cs : ℝ)
    (hX : 2 ≤ X) (hN : (N : ℝ) ≤ X) (hd : 1 ≤ d) (hdX : (d : ℝ) ≤ X)
    (hB : 0 ≤ B) (hCs : 0 ≤ Cs)
    (hW : ∀ m ∈ Finset.range (N + 1),
      |w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤ B)
    (hS : |singSeries N / psiN N d| ≤ Cs * Real.log X ^ 2 / d) :
    ‖Rdl w₁ w₂ X N d l‖ ≤ (2 * B * (1 + Cs)) * X / d * Real.log X ^ 2 := by
  have hcount := residue_count_le221 X N d l hN hd hdX
  have hmass : (N : ℝ) + 1 ≤ 2 * X := by linarith
  apply (Rdl_triangle_explicit221 w₁ w₂ X N d l B hX hN hB hW).trans
  calc
    _ ≤ B * Real.log X ^ 2 * (2 * X / d) +
        (Cs * Real.log X ^ 2 / d) * (B * (2 * X)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hcount (mul_nonneg hB (sq_nonneg _))
      · exact mul_le_mul hS (mul_le_mul_of_nonneg_left hmass hB)
          (by positivity) (by positivity)
    _ = _ := by ring

/-- Page 7 proof of Theorem 1.1. moment_threshold221. -/
theorem moment_threshold221 {L X C D E A s z : ℝ} (hL : 0 < L) (hX : 0 ≤ X)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hmoment : s ^ 2 ≤ C * X * L ^ E * z)
    (hzero : z ≤ D * X / L ^ (2 * A + E)) :
    s ≤ Real.sqrt (C * D) * X / L ^ A := by
  have hpow : L ^ (2 * A + E) = (L ^ A) ^ 2 * L ^ E := by
    rw [Real.rpow_add hL]
    congr 1
    rw [mul_comm (2 : ℝ), Real.rpow_mul hL.le, Real.rpow_two]
  have hLp : 0 < L ^ A := Real.rpow_pos_of_pos hL _
  have hLe : 0 < L ^ E := Real.rpow_pos_of_pos hL _
  have hb : s ^ 2 ≤ C * D * X ^ 2 / (L ^ A) ^ 2 := by
    apply hmoment.trans
    calc
      C * X * L ^ E * z ≤ C * X * L ^ E * (D * X / L ^ (2 * A + E)) :=
        mul_le_mul_of_nonneg_left hzero (by positivity)
      _ = _ := by rw [hpow]; field_simp
  have hsqrt := Real.sq_sqrt (mul_nonneg hC hD)
  have ht : (Real.sqrt (C * D) * X / L ^ A) ^ 2 =
      C * D * X ^ 2 / (L ^ A) ^ 2 := by
    rw [div_pow, mul_pow, hsqrt]
  have ht0 : 0 ≤ Real.sqrt (C * D) * X / L ^ A := by positivity
  nlinarith only [hb, ht, ht0, sq_nonneg (s - Real.sqrt (C * D) * X / L ^ A)]

/-- Page 7 proof of Theorem 1.1. excCount_le_scale221. -/
theorem excCount_le_scale221 (S P : ℕ → Prop) {X : ℝ} (hX : 0 ≤ X) :
    (excCount S P X : ℝ) ≤ X := by
  classical
  have h : excCount S P X ≤ ⌊X⌋₊ := by
    unfold excCount
    calc
      _ ≤ (Finset.Icc 1 ⌊X⌋₊).card := Finset.card_filter_le _ _
      _ = _ := by simp
  exact (show (excCount S P X : ℝ) ≤ ⌊X⌋₊ by exact_mod_cast h).trans (Nat.floor_le hX)

/-- Page 7 proof of Theorem 1.1. excCount_mono_on_range221. -/
theorem excCount_mono_on_range221 (S P Q : ℕ → Prop) (X : ℝ)
    (hPQ : ∀ N ∈ Finset.Icc 1 ⌊X⌋₊, P N → Q N) :
    excCount S Q X ≤ excCount S P X := by
  classical
  unfold excCount
  apply Finset.card_le_card
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  rcases hN with ⟨hI, hhalf, hS, hQ⟩
  exact ⟨hI, hhalf, hS, fun hP => hQ (hPQ N hI hP)⟩

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. zero_moment_of_beta221. -/
theorem zero_moment_of_beta221 (θ η : ℝ) (hbeta : BetaLevel θ η) (w₁ w₂ : ℝ → ℝ)
    (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂)
    (hPNT : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      ∀ N : ℕ, N ≤ ⌊X⌋₊ →
        (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d|) *
          |∑ m ∈ Finset.range (N + 1),
            (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤
              C * X / Real.log X ^ A) :
    ∀ A : ℝ, 0 < A → ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X →
      (excCount (fun _ => True)
        (fun N => levelSum θ 0 w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ)
          ≤ C₁ * X / Real.log X ^ A := by
  classical
  intro A hA
  obtain ⟨C₁, C₂, hb⟩ := betaLevel_lambda221 θ η hbeta w₁ w₂ hw₁ hw₂ A hA
  obtain ⟨C, hP⟩ := hPNT A hA
  refine ⟨C₁, C₂ + C, fun X hX => ?_⟩
  have he : excCount (fun _ => True)
      (fun N => levelSum θ 0 w₁ w₂ X N ≤ (C₂ + C) * X / Real.log X ^ A) X ≤
      excCount (fun _ => True)
      (fun N => betaSum θ (fun n => Λ n) w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X := by
    unfold excCount
    apply Finset.card_le_card
    intro N hN
    simp only [Finset.mem_filter] at hN ⊢
    rcases hN with ⟨hI, hhalf, htrue, hbad⟩
    refine ⟨hI, hhalf, htrue, fun hg => hbad ?_⟩
    calc
      levelSum θ 0 w₁ w₂ X N ≤ _ := levelSum_zero_le_beta221 θ X N w₁ w₂
      _ ≤ C₂ * X / Real.log X ^ A + C * X / Real.log X ^ A :=
        add_le_add hg (hP X hX N (Finset.mem_Icc.mp hI).2)
      _ = _ := by ring
  exact (show (excCount (fun _ => True)
      (fun N => levelSum θ 0 w₁ w₂ X N ≤ (C₂ + C) * X / Real.log X ^ A) X : ℝ) ≤
      (excCount (fun _ => True)
      (fun N => betaSum θ (fun n => Λ n) w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ)
      from by exact_mod_cast he).trans (hb X hX)

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. levelGP_of_zero_moment221. -/
theorem levelGP_of_zero_moment221 (θ : ℝ)
    (hzero : ∀ A : ℝ, 0 < A → ∀ η : ℝ, 0 < η → ∀ w₁ w₂ : ℝ → ℝ,
      SmoothWeight η w₁ → SmoothWeight η w₂ →
      ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X →
        (excCount (fun _ => True)
          (fun N => levelSum θ 0 w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ) ≤
            C₁ * X / Real.log X ^ A)
    (hmoment : ∀ k : ℕ, ∀ η : ℝ, 0 < η → ∀ w₁ w₂ : ℝ → ℝ,
      SmoothWeight η w₁ → SmoothWeight η w₂ →
      ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
        levelSum θ k w₁ w₂ X N ^ 2 ≤
          C * X * Real.log X ^ E * levelSum θ 0 w₁ w₂ X N) : LevelGP θ := by
  intro A hA k η hη w₁ w₂ hw₁ hw₂
  obtain ⟨C, E, hC, hE, hm⟩ := hmoment k η hη w₁ w₂ hw₁ hw₂
  have hB : 0 < 2 * A + E := by linarith
  obtain ⟨C₁, C₂, hb⟩ := hzero (2 * A + E) hB η hη w₁ w₂ hw₁ hw₂
  let D := max C₂ 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨max 1 C₁, Real.sqrt (C * D), fun X hX => ?_⟩
  have hX0 : 0 ≤ X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL _
  have hLB : 0 < Real.log X ^ (2 * A + E) := Real.rpow_pos_of_pos hL _
  have he : excCount (fun _ => True)
      (fun N => levelSum θ k w₁ w₂ X N ≤ Real.sqrt (C * D) * X / Real.log X ^ A) X ≤
      excCount (fun _ => True)
      (fun N => levelSum θ 0 w₁ w₂ X N ≤ C₂ * X / Real.log X ^ (2 * A + E)) X := by
    apply excCount_mono_on_range221
    intro N hN hg
    have hg' : levelSum θ 0 w₁ w₂ X N ≤ D * X / Real.log X ^ (2 * A + E) :=
      hg.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0) hLB.le)
    exact moment_threshold221 hL hX0 hC hD (hm X hX N (Finset.mem_Icc.mp hN).2) hg'
  by_cases hL1 : 1 ≤ Real.log X
  · calc
      _ ≤ (excCount (fun _ => True)
          (fun N => levelSum θ 0 w₁ w₂ X N ≤ C₂ * X / Real.log X ^ (2 * A + E)) X : ℝ) := by
            exact_mod_cast he
      _ ≤ C₁ * X / Real.log X ^ (2 * A + E) := hb X hX
      _ ≤ max 1 C₁ * X / Real.log X ^ (2 * A + E) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hX0) hLB.le
      _ ≤ max 1 C₁ * X / Real.log X ^ A :=
        div_le_div_of_nonneg_left (mul_nonneg (by positivity) hX0) hLA
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  · apply (excCount_le_scale221 _ _ hX0).trans
    apply (le_div_iff₀ hLA).2
    have hp : Real.log X ^ A ≤ 1 := Real.rpow_le_one hL.le (le_of_not_ge hL1) hA.le
    exact (mul_le_of_le_one_right hX0 hp).trans
      (le_mul_of_one_le_left hX0 (le_max_left _ _))

/-- Page 7 proof of Theorem 1.1. divisorHarmonic221. -/
noncomputable def divisorHarmonic221 (r M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ r / n

/-- Page 7 proof of Theorem 1.1. divisor_moment_convolution221. -/
theorem divisor_moment_convolution221 (r n : ℕ) :
    (n.divisors.card : ℝ) ^ (r + 1) ≤
      ∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ r * ((n / d).divisors.card : ℝ) ^ r := by
  classical
  calc
    _ = ∑ d ∈ n.divisors, (n.divisors.card : ℝ) ^ r := by
      simp [pow_succ, mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      have hdn := Nat.dvd_of_mem_divisors hd
      have hτ : n.divisors.card ≤ d.divisors.card * (n / d).divisors.card := by
        calc
          _ = (d * (n / d)).divisors.card := by rw [Nat.mul_div_cancel' hdn]
          _ ≤ _ := by rw [Nat.divisors_mul]; exact Finset.card_mul_le
      have hτR : (n.divisors.card : ℝ) ≤ (d.divisors.card : ℝ) * ((n / d).divisors.card : ℝ) := by
        exact_mod_cast hτ
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n.divisors.card) hτR r

/-- Page 7 proof of Theorem 1.1. divisorHarmonic_recurrence221. -/
theorem divisorHarmonic_recurrence221 (r M : ℕ) : divisorHarmonic221 (r + 1) M ≤ divisorHarmonic221 r M ^ 2 := by
  classical
  let s := (Finset.Icc 1 M).sigma (fun n => n.divisors)
  let t := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  let e : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2, p.1 / p.2)
  have hmul : ∀ p ∈ s, p.2 * (p.1 / p.2) = p.1 := by
    intro p hp
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).2)
  have hinj : Set.InjOn e (s : Set (Σ _ : ℕ, ℕ)) := by
    intro p hp q hq he
    have hd : p.2 = q.2 := congrArg Prod.fst he
    have hquot : p.1 / p.2 = q.1 / q.2 := congrArg Prod.snd he
    have hn : p.1 = q.1 := by
      calc
        p.1 = p.2 * (p.1 / p.2) := (hmul p hp).symm
        _ = q.2 * (q.1 / q.2) := by rw [hquot, hd]
        _ = q.1 := hmul q hq
    exact Sigma.ext hn (heq_of_eq hd)
  have hmap : Finset.image e s ⊆ t := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hn := Finset.mem_Icc.mp (Finset.mem_sigma.mp hp).1
    have hd := (Finset.mem_sigma.mp hp).2
    have hqpos : 1 ≤ p.1 / p.2 := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro he
      have hh := hmul p hp
      rw [he, mul_zero] at hh
      omega
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd, (Nat.divisor_le hd).trans hn.2⟩,
      Finset.mem_Icc.mpr ⟨hqpos, (Nat.div_le_self _ _).trans hn.2⟩⟩
  have hsum : (∑ p ∈ s, (p.2.divisors.card : ℝ) ^ r * ((p.1 / p.2).divisors.card : ℝ) ^ r / p.1) ≤
      ∑ p ∈ t, ((p.1.divisors.card : ℝ) ^ r / p.1) * ((p.2.divisors.card : ℝ) ^ r / p.2) := by
    apply Finset.sum_le_sum_of_injOn e hinj hmap
    · intro p hp
      dsimp only [e]
      rw [div_mul_div_comm, ← Nat.cast_mul, hmul p hp]
    · intro p hp hn
      positivity
  unfold divisorHarmonic221
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        (∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ r * ((n / d).divisors.card : ℝ) ^ r) / n := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right (divisor_moment_convolution221 r n) (Nat.cast_nonneg _)
    _ = ∑ p ∈ s, (p.2.divisors.card : ℝ) ^ r * ((p.1 / p.2).divisors.card : ℝ) ^ r / p.1 := by
      simp_rw [Finset.sum_div]
      exact Finset.sum_sigma' _ _ _
    _ ≤ _ := hsum
    _ = _ := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Page 7 proof of Theorem 1.1. divisorHarmonic_log_bound221. -/
theorem divisorHarmonic_log_bound221 (r M : ℕ) : divisorHarmonic221 r M ≤ (1 + Real.log M) ^ (2 ^ r) := by
  induction r with
  | zero =>
    simpa only [divisorHarmonic221, pow_zero, pow_one, one_div,
      harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log M
  | succ r ih =>
    apply (divisorHarmonic_recurrence221 r M).trans
    calc
      divisorHarmonic221 r M ^ 2 ≤ ((1 + Real.log M) ^ (2 ^ r)) ^ 2 :=
        pow_le_pow_left₀ (by unfold divisorHarmonic221; positivity) ih 2
      _ = _ := by rw [← pow_mul, pow_succ]

/-- Page 7 proof of Theorem 1.1. divisor_moment_log_budget221. -/
theorem divisor_moment_log_budget221 (θ : ℝ) (r : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ X : ℝ, 2 ≤ X →
      (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, (d.divisors.card : ℝ) ^ r / d) ≤
        C * Real.log X ^ E := by
  let K := 1 / Real.log 2 + max θ 0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K ^ (2 ^ r), (2 ^ r : ℕ), by positivity, by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hL2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  by_cases hM : ⌊X ^ θ⌋₊ = 0
  · simp only [hM, Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), Finset.sum_empty]
    positivity
  · have hMpos : (0 : ℝ) < (⌊X ^ θ⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hM
    have hlogM : Real.log (⌊X ^ θ⌋₊ : ℕ) ≤ θ * Real.log X := by
      calc
        _ ≤ Real.log (X ^ θ) := Real.log_le_log hMpos (Nat.floor_le (Real.rpow_nonneg hX0.le _))
        _ = _ := by rw [Real.log_rpow hX0]
    have hOne : 1 ≤ (1 / Real.log 2) * Real.log X := by
      rw [one_div_mul_eq_div, le_div_iff₀ hlog2]
      simpa using hL2
    have hbase : 1 + Real.log (⌊X ^ θ⌋₊ : ℕ) ≤ K * Real.log X := by
      have ht := mul_le_mul_of_nonneg_right (le_max_left θ 0) hLX.le
      dsimp [K]
      nlinarith
    have hbase0 : 0 ≤ 1 + Real.log (⌊X ^ θ⌋₊ : ℕ) := by
      have hMone : (1 : ℝ) ≤ (⌊X ^ θ⌋₊ : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
      have := Real.log_nonneg hMone
      linarith
    calc
      _ ≤ (1 + Real.log (⌊X ^ θ⌋₊ : ℕ)) ^ (2 ^ r) := divisorHarmonic_log_bound221 r _
      _ ≤ (K * Real.log X) ^ (2 ^ r) := pow_le_pow_left₀ hbase0 hbase _
      _ = _ := by rw [mul_pow, Real.rpow_natCast]

/-- Page 7 proof of Theorem 1.1. finite_abel_variation221. -/
theorem finite_abel_variation221 (n : ℕ) (a b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpartial : ∀ m ≤ n, |∑ i ∈ Finset.range m, a i| ≤ C) :
    |∑ i ∈ Finset.range n, b i * a i| ≤
      C * (|b (n - 1)| + ∑ i ∈ Finset.range (n - 1), |b (i + 1) - b i|) := by
  have he := Finset.sum_range_by_parts b a n
  simp only [smul_eq_mul] at he
  rw [he]
  calc
    _ ≤ |b (n - 1) * ∑ i ∈ Finset.range n, a i| +
        |∑ i ∈ Finset.range (n - 1), (b (i + 1) - b i) * ∑ j ∈ Finset.range (i + 1), a j| :=
      abs_sub _ _
    _ ≤ |b (n - 1)| * C +
        ∑ i ∈ Finset.range (n - 1), |b (i + 1) - b i| * C := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) (abs_nonneg _)
      · apply (abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpartial (i + 1) (by have := Finset.mem_range.mp hi; omega))
          (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. moment_bound_of_pointwise221. -/
theorem moment_bound_of_pointwise221 (θ : ℝ) (k : ℕ) (w₁ w₂ : ℝ → ℝ)
    (hpointwise : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
        (supR w₁ w₂ X N d : ℝ) ≤ C * X / d * Real.log X ^ 2) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      levelSum θ k w₁ w₂ X N ^ 2 ≤ C * X * Real.log X ^ E * levelSum θ 0 w₁ w₂ X N := by
  obtain ⟨C₀, hC₀, hp⟩ := hpointwise
  obtain ⟨H, E, hH, hE, hb⟩ := divisor_moment_log_budget221 θ (2 * k)
  refine ⟨C₀ * H, E + 2, mul_nonneg hC₀ hH, by linarith, fun X hX N hN => ?_⟩
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hzero : 0 ≤ levelSum θ 0 w₁ w₂ X N := by unfold levelSum; positivity
  calc
    _ ≤ (C₀ * X * Real.log X ^ 2 *
        ∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, (d.divisors.card : ℝ) ^ (2 * k) / d) *
          levelSum θ 0 w₁ w₂ X N :=
      levelSum_square_cauchy221 θ X k N w₁ w₂ C₀ hX hC₀ (hp X hX N hN)
    _ ≤ (C₀ * X * Real.log X ^ 2 * (H * Real.log X ^ E)) * levelSum θ 0 w₁ w₂ X N := by
      apply mul_le_mul_of_nonneg_right _ hzero
      exact mul_le_mul_of_nonneg_left (hb X hX) (by positivity)
    _ = _ := by rw [Real.rpow_add hL, Real.rpow_two]; ring

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. levelGP_of_beta_PNT_pointwise221. -/
theorem levelGP_of_beta_PNT_pointwise221 (θ : ℝ)
    (h31 : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η)
    (hPNT : ∀ η : ℝ, 0 < η → ∀ w₁ w₂ : ℝ → ℝ,
      SmoothWeight η w₁ → SmoothWeight η w₂ →
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
        (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d|) *
          |∑ m ∈ Finset.range (N + 1),
            (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤
              C * X / Real.log X ^ A)
    (hpointwise : ∀ η : ℝ, 0 < η → ∀ w₁ w₂ : ℝ → ℝ,
      SmoothWeight η w₁ → SmoothWeight η w₂ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
        ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
          (supR w₁ w₂ X N d : ℝ) ≤ C * X / d * Real.log X ^ 2) : LevelGP θ := by
  apply levelGP_of_zero_moment221 θ
  · intro A hA η hη w₁ w₂ hw₁ hw₂
    obtain ⟨η₀, hη₀, hb⟩ := h31
    let η' := min η η₀
    have hη' : 0 < η' := lt_min hη hη₀
    have hw₁' : SmoothWeight η' w₁ :=
      ⟨hw₁.1, hw₁.2.trans (Set.Icc_subset_Icc_left (min_le_left _ _))⟩
    have hw₂' : SmoothWeight η' w₂ :=
      ⟨hw₂.1, hw₂.2.trans (Set.Icc_subset_Icc_left (min_le_left _ _))⟩
    exact zero_moment_of_beta221 θ η' (hb η' hη' (min_le_right _ _))
      w₁ w₂ hw₁' hw₂' (hPNT η' hη' w₁ w₂ hw₁' hw₂') A hA
  · intro k η hη w₁ w₂ hw₁ hw₂
    exact moment_bound_of_pointwise221 θ k w₁ w₂ (hpointwise η hη w₁ w₂ hw₁ hw₂)

/-- Page 7 proof of Theorem 1.1. smoothWeight_bounds221. -/
theorem smoothWeight_bounds221 (η : ℝ) (w : ℝ → ℝ) (hw : SmoothWeight η w) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ (∀ x : ℝ, |w x| ≤ B) ∧
      ∀ x y : ℝ, |w x - w y| ≤ L * |x - y| := by
  have hcompact : HasCompactSupport w :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hw.2
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuous hw.1.continuous
  have hderiv : Continuous (deriv w) := hw.1.continuous_deriv (by simp)
  obtain ⟨L, hL⟩ := hcompact.deriv.exists_bound_of_continuous hderiv
  refine ⟨max B 0, max L 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro x
    exact (show |w x| ≤ B by simpa only [Real.norm_eq_abs] using hB x).trans (le_max_left _ _)
  · intro x y
    have hh := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (f := w) (C := max L 0)
      (fun z hz => hw.1.differentiable (by simp) z)
      (fun z hz => (hL z).trans (le_max_left _ _))
      (Set.mem_univ y) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using hh

/-- Page 7 proof of Theorem 1.1. level_sums_empty221. -/
theorem level_sums_empty221 {θ X : ℝ} (hθ : θ < 0) (hX : 2 ≤ X) (k N : ℕ)
    (w₁ w₂ : ℝ → ℝ) (b : ℕ → ℝ) :
    levelSum θ k w₁ w₂ X N = 0 ∧ betaSum θ b w₁ w₂ X N = 0 ∧
      betaSum' θ b w₁ w₂ X N = 0 := by
  have hp : X ^ θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hθ
  have hf : ⌊X ^ θ⌋₊ = 0 := Nat.floor_eq_zero.mpr hp
  simp [levelSum, betaSum, betaSum', hf]

/-- Page 7 proof of Theorem 1.1. betaLevel_negative221. -/
theorem betaLevel_negative221 {θ : ℝ} (hθ : θ < 0) (η : ℝ) : BetaLevel θ η := by
  intro k hk w₁ w₂ hw₁ hw₂ A hA
  refine ⟨0, 0, fun X hX lo hi hadm => ?_⟩
  have hβ : ∀ N : ℕ, betaSum θ (beta k lo hi) w₁ w₂ X N = 0 :=
    fun N => (level_sums_empty221 hθ hX k N w₁ w₂ (beta k lo hi)).2.1
  have hβ' : ∀ N : ℕ, betaSum' θ (beta k lo hi) w₁ w₂ X N = 0 :=
    fun N => (level_sums_empty221 hθ hX k N w₁ w₂ (beta k lo hi)).2.2
  simp [hβ, hβ', excCount]

/-- Page 7 proof of Theorem 1.1. levelGP_negative221. -/
theorem levelGP_negative221 {θ : ℝ} (hθ : θ < 0) : LevelGP θ := by
  intro A hA k η hη w₁ w₂ hw₁ hw₂
  refine ⟨0, 0, fun X hX => ?_⟩
  have hlevel : ∀ N : ℕ, levelSum θ k w₁ w₂ X N = 0 :=
    fun N => (level_sums_empty221 hθ hX k N w₁ w₂ (fun _ => 0)).1
  simp [hlevel, excCount]

/-- Page 7 proof of Theorem 1.1. smooth_product_bounds221. -/
theorem smooth_product_bounds221 (η : ℝ) (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧
      (∀ t x : ℝ, |w₁ (t - x) * w₂ x| ≤ B) ∧
      ∀ t x y : ℝ, |w₁ (t - x) * w₂ x - w₁ (t - y) * w₂ y| ≤ L * |x - y| := by
  obtain ⟨B₁, L₁, hB₁, hL₁, hb₁, hl₁⟩ := smoothWeight_bounds221 η w₁ hw₁
  obtain ⟨B₂, L₂, hB₂, hL₂, hb₂, hl₂⟩ := smoothWeight_bounds221 η w₂ hw₂
  refine ⟨B₁ * B₂, L₁ * B₂ + B₁ * L₂, by positivity, by positivity, ?_, ?_⟩
  · intro t x
    rw [abs_mul]
    exact mul_le_mul (hb₁ _) (hb₂ _) (abs_nonneg _) hB₁
  · intro t x y
    have hdiff : |(t - x) - (t - y)| = |x - y| := by
      rw [show (t - x) - (t - y) = -(x - y) by ring, abs_neg]
    calc
      _ = |(w₁ (t - x) - w₁ (t - y)) * w₂ x + w₁ (t - y) * (w₂ x - w₂ y)| := by
        congr 1
        ring
      _ ≤ |(w₁ (t - x) - w₁ (t - y)) * w₂ x| + |w₁ (t - y) * (w₂ x - w₂ y)| := abs_add_le _ _
      _ ≤ (L₁ * |x - y|) * B₂ + B₁ * (L₂ * |x - y|) := by
        simp only [abs_mul]
        apply add_le_add
        · exact mul_le_mul (by simpa only [hdiff] using hl₁ (t - x) (t - y)) (hb₂ x)
            (abs_nonneg _) (by positivity)
        · exact mul_le_mul (hb₁ _) (hl₂ x y) (abs_nonneg _) hB₁
      _ = _ := by ring

noncomputable def pntWeight221 (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N i : ℕ) : ℝ :=
  w₁ (((N : ℝ) - i) / X) * w₂ ((i : ℝ) / X)


/-- Page 7 proof of Theorem 1.1. pntWeight_variation221. -/
theorem pntWeight_variation221 (η : ℝ) (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      |pntWeight221 w₁ w₂ X N N| +
        ∑ i ∈ Finset.range N, |pntWeight221 w₁ w₂ X N (i + 1) - pntWeight221 w₁ w₂ X N i| ≤ V := by
  obtain ⟨B, L, hB, hL, hb, hl⟩ := smooth_product_bounds221 η w₁ w₂ hw₁ hw₂
  refine ⟨B + L, add_nonneg hB hL, fun X hX N hN => ?_⟩
  have hX0 : 0 < X := by linarith
  have hNX : (N : ℝ) ≤ X := (show (N : ℝ) ≤ ⌊X⌋₊ by exact_mod_cast hN).trans (Nat.floor_le hX0.le)
  have hfun : ∀ i : ℕ, pntWeight221 w₁ w₂ X N i =
      w₁ ((N : ℝ) / X - (i : ℝ) / X) * w₂ ((i : ℝ) / X) := by
    intro i
    simp only [pntWeight221, sub_div]
  have hstep : ∀ i : ℕ, |pntWeight221 w₁ w₂ X N (i + 1) - pntWeight221 w₁ w₂ X N i| ≤ L / X := by
    intro i
    have hh := hl ((N : ℝ) / X) (((i + 1 : ℕ) : ℝ) / X) ((i : ℝ) / X)
    have hdiff : |(((i + 1 : ℕ) : ℝ) / X) - ((i : ℝ) / X)| = 1 / X := by
      rw [show (((i + 1 : ℕ) : ℝ) / X) - ((i : ℝ) / X) = 1 / X by push_cast; ring]
      exact abs_of_nonneg (by positivity)
    simpa only [hfun, hdiff, mul_one_div] using hh
  calc
    _ ≤ B + ∑ i ∈ Finset.range N, L / X := by
      apply add_le_add
      · simpa only [hfun] using hb ((N : ℝ) / X) ((N : ℝ) / X)
      · exact Finset.sum_le_sum (fun i hi => hstep i)
    _ = B + L * (N / X) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ B + L := by
      have hh : (N : ℝ) / X ≤ 1 := (div_le_one hX0).mpr hNX
      exact add_le_add le_rfl (mul_le_of_le_one_right hL hh)

/-- Page 7 proof of Theorem 1.1. pnt_correction_eq221. -/
theorem pnt_correction_eq221 (N : ℕ) (X : ℝ) (w₁ w₂ : ℝ → ℝ) :
    (∑ m ∈ Finset.range (N + 1),
      (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)) =
    ∑ n ∈ Finset.range (N + 1), pntWeight221 w₁ w₂ X N n * (Λ n - 1) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := by simpa using Finset.mem_range.mp hn
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hnN, pntWeight221, Nat.cast_sub hnN]
  ring

/-- Page 7 proof of Theorem 1.1. pnt_correction_of_partial221. -/
theorem pnt_correction_of_partial221 (N : ℕ) (X : ℝ) (w₁ w₂ : ℝ → ℝ) (C V : ℝ)
    (hC : 0 ≤ C)
    (hpartial : ∀ m ≤ N + 1, |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C)
    (hvariation : |pntWeight221 w₁ w₂ X N N| +
      ∑ i ∈ Finset.range N, |pntWeight221 w₁ w₂ X N (i + 1) - pntWeight221 w₁ w₂ X N i| ≤ V) :
    |∑ m ∈ Finset.range (N + 1),
      (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤ C * V := by
  rw [pnt_correction_eq221]
  have h := finite_abel_variation221 (N + 1) (fun i => Λ i - 1) (pntWeight221 w₁ w₂ X N) C hC hpartial
  simp only [Nat.add_sub_cancel] at h
  exact h.trans (mul_le_mul_of_nonneg_left hvariation hC)

example
    (hPNTpartial : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ m : ℕ, m ≤ ⌊X⌋₊ + 1 →
        |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * X / Real.log X ^ A)
    (η : ℝ) (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂)
    (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      |∑ m ∈ Finset.range (N + 1),
        (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤
          K * X / Real.log X ^ A := by
  obtain ⟨V, hV, hv⟩ := pntWeight_variation221 η w₁ w₂ hw₁ hw₂
  obtain ⟨C, hC, hc⟩ := hPNTpartial A hA
  refine ⟨C * V, mul_nonneg hC hV, fun X hX N hN => ?_⟩
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hC' : 0 ≤ C * X / Real.log X ^ A := by positivity
  have hh := pnt_correction_of_partial221 N X w₁ w₂ (C * X / Real.log X ^ A) V hC'
    (fun m hm => hc X hX m (hm.trans (Nat.succ_le_succ hN))) (hv X hX N hN)
  convert hh using 1 <;> ring

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. weightedPNT_of_partial221. -/
theorem weightedPNT_of_partial221 (hPNTpartial : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ m : ℕ, m ≤ ⌊X⌋₊ + 1 →
        |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * X / Real.log X ^ A)
    (η : ℝ) (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂)
    (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      |∑ m ∈ Finset.range (N + 1),
        (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤
          K * X / Real.log X ^ A := by
  obtain ⟨V, hV, hv⟩ := pntWeight_variation221 η w₁ w₂ hw₁ hw₂
  obtain ⟨C, hC, hc⟩ := hPNTpartial A hA
  refine ⟨C * V, mul_nonneg hC hV, fun X hX N hN => ?_⟩
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hC' : 0 ≤ C * X / Real.log X ^ A := by positivity
  have hh := pnt_correction_of_partial221 N X w₁ w₂ (C * X / Real.log X ^ A) V hC'
    (fun m hm => hc X hX m (hm.trans (Nat.succ_le_succ hN))) (hv X hX N hN)
  convert hh using 1 <;> ring

/-- Page 8 Lemma 3.2. tauCharacter221. -/
noncomputable def tauCharacter221 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℤ) : ℂ :=
  ∑ a : (ZMod q)ˣ, χ a * e (-(m : ℝ) * ((a : ZMod q).val : ℝ) / q)

/-- Cited page 8 Lemma 3.2. This Prop is an input, not a theorem. -/
def GaussBounds32_221 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    ‖tauCharacter221 q χ (-1)‖ ≤ Real.sqrt (χ.conductor : ℝ) ∧
    ∀ m : ℤ, ‖tauCharacter221 q χ m‖ ≤ Real.sqrt ((q : ℝ) * (Int.gcd m q : ℝ))


/-- Page 8 Lemma 3.2. gauss_crude_bound221. -/
theorem gauss_crude_bound221 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℤ) :
    ‖tauCharacter221 q χ m‖ ≤ (q.totient : ℝ) := by
  have he : ∀ x : ℝ, ‖e x‖ = 1 := by
    intro x
    simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  unfold tauCharacter221
  calc
    _ ≤ ∑ a : (ZMod q)ˣ, ‖χ a * e (-(m : ℝ) * ((a : ZMod q).val : ℝ) / q)‖ := norm_sum_le _ _
    _ = _ := by simp [norm_mul, he, ZMod.card_units_eq_totient]

/-- Page 8 Lemma 3.2. gauss_crude_not_sqrt221. -/
theorem gauss_crude_not_sqrt221 : Real.sqrt 3 < ((3 : ℕ).totient : ℝ) := by
  rw [Nat.totient_prime (by decide : Nat.Prime 3)]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr
  norm_num

/-- Page 8 Lemma 3.2. tauCharacter_mod_one221. -/
theorem tauCharacter_mod_one221 (χ : DirichletCharacter ℂ 1) (m : ℤ) : tauCharacter221 1 χ m = 1 := by
  have hu : (Finset.univ : Finset (ZMod 1)ˣ) = {1} := by
    ext a
    constructor
    · intro h
      exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
    · intro h
      exact Finset.mem_univ _
  rw [tauCharacter221, hu, Finset.sum_singleton]
  simp only [Units.val_one, Nat.cast_one, map_one]
  have hv : (1 : ZMod 1).val = 0 := by decide
  rw [hv]
  simp [e]

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. pnt_correction_budget221. -/
theorem pnt_correction_budget221 (θ : ℝ)
    (hPNTpartial : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ m : ℕ, m ≤ ⌊X⌋₊ + 1 →
        |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * X / Real.log X ^ A)
    (hArithmetic : ∃ H E : ℝ, 0 ≤ H ∧ 0 ≤ E ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d|) ≤ H * Real.log X ^ E)
    (η : ℝ) (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d|) *
        |∑ m ∈ Finset.range (N + 1),
          (Λ (N - m) - 1) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤
            C * X / Real.log X ^ A := by
  obtain ⟨H, E, hH, hE, ha⟩ := hArithmetic
  obtain ⟨K, hK, hb⟩ := weightedPNT_of_partial221 hPNTpartial η w₁ w₂ hw₁ hw₂
    (A + E) (by linarith)
  refine ⟨H * K, fun X hX N hN => ?_⟩
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  calc
    _ ≤ (H * Real.log X ^ E) * (K * X / Real.log X ^ (A + E)) :=
      mul_le_mul (ha X hX N hN) (hb X hX N hN) (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlog]
      field_simp

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. arithmetic_budget_of_singular221. -/
theorem arithmetic_budget_of_singular221 (θ : ℝ)
    (hSingular : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d| ≤ Cs * Real.log X ^ 2 / d) :
    ∃ H E : ℝ, 0 ≤ H ∧ 0 ≤ E ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d|) ≤ H * Real.log X ^ E := by
  obtain ⟨Cs, hCs, hs⟩ := hSingular
  obtain ⟨H, E, hH, hE, hb⟩ := divisor_moment_log_budget221 θ 0
  refine ⟨Cs * H, E + 2, mul_nonneg hCs hH, by linarith, fun X hX N hN => ?_⟩
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hb' : (∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, (1 : ℝ) / d) ≤ H * Real.log X ^ E := by
    simpa only [pow_zero] using hb X hX
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, Cs * Real.log X ^ 2 / d :=
      Finset.sum_le_sum (fun d hd => hs X hX N hN d hd)
    _ = Cs * Real.log X ^ 2 * ∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, (1 : ℝ) / d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ Cs * Real.log X ^ 2 * (H * Real.log X ^ E) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by rw [Real.rpow_add hlog, Real.rpow_two]; ring

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. pointwise_of_singular221. -/
theorem pointwise_of_singular221 (θ : ℝ) (hθ : θ ≤ 1)
    (hSingular : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d| ≤ Cs * Real.log X ^ 2 / d)
    (η : ℝ) (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight η w₁) (hw₂ : SmoothWeight η w₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
        (supR w₁ w₂ X N d : ℝ) ≤ C * X / d * Real.log X ^ 2 := by
  obtain ⟨Cs, hCs, hs⟩ := hSingular
  obtain ⟨B, L, hB, hL, hb, hl⟩ := smooth_product_bounds221 η w₁ w₂ hw₁ hw₂
  refine ⟨2 * B * (1 + Cs), by positivity, fun X hX N hN d hd => ?_⟩
  have hX0 : 0 < X := by linarith
  have hNX : (N : ℝ) ≤ X := (show (N : ℝ) ≤ ⌊X⌋₊ by exact_mod_cast hN).trans (Nat.floor_le hX0.le)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdX : (d : ℝ) ≤ X := by
    calc
      _ ≤ ((⌊X ^ θ⌋₊ : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).2
      _ ≤ X ^ θ := Nat.floor_le (Real.rpow_nonneg hX0.le _)
      _ ≤ X := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ X) hθ
  have hW : ∀ m ∈ Finset.range (N + 1),
      |w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)| ≤ B := by
    intro m hm
    simpa using hb ((m : ℝ) / X + ((N - m : ℕ) : ℝ) / X) (((N - m : ℕ) : ℝ) / X)
  have hbound : 0 ≤ (2 * B * (1 + Cs)) * X / d * Real.log X ^ 2 := by positivity
  have hh : supR w₁ w₂ X N d ≤
      (⟨(2 * B * (1 + Cs)) * X / d * Real.log X ^ 2, hbound⟩ : NNReal) := by
    apply Finset.sup_le
    intro l hl
    exact_mod_cast Rdl_pointwise_constant221 w₁ w₂ X N d l B Cs hX hNX hd1 hdX hB hCs hW (hs X hX N hN d hd)
  exact_mod_cast hh

/-- Page 7 proof of Theorem 1.1. CONDITIONAL ON the named input bounds. levelGP_of_thm31_PNT_singular221. -/
theorem levelGP_of_thm31_PNT_singular221 (θ : ℝ) (hθ : θ ≤ 1)
    (h31 : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η)
    (hPNTpartial : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ m : ℕ, m ≤ ⌊X⌋₊ + 1 →
        |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * X / Real.log X ^ A)
    (hSingular : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ X : ℝ, 2 ≤ X → ∀ N : ℕ, N ≤ ⌊X⌋₊ →
      ∀ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, |singSeries N / psiN N d| ≤ Cs * Real.log X ^ 2 / d) :
    LevelGP θ := by
  apply levelGP_of_beta_PNT_pointwise221 θ h31
  · intro η hη w₁ w₂ hw₁ hw₂
    exact pnt_correction_budget221 θ hPNTpartial (arithmetic_budget_of_singular221 θ hSingular)
      η w₁ w₂ hw₁ hw₂
  · intro η hη w₁ w₂ hw₁ hw₂
    exact pointwise_of_singular221 θ hθ hSingular η w₁ w₂ hw₁ hw₂

/-- Page 7 PNT step. Uniform truncation from the ordinary pointwise logarithmic PNT.
CONDITIONAL ON the named pointwise PNT schema. -/
theorem uniform_partial_of_pointwise221
    (hPNTpoint : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * m / Real.log (m : ℝ) ^ A) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ m : ℕ, m ≤ ⌊X⌋₊ + 1 →
        |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * X / Real.log X ^ A := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C₁, hC₁, hb₁⟩ := hPNTpoint 1 (by norm_num)
  let G := max 1 (C₁ / Real.log 2)
  have hG : 0 ≤ G := (by dsimp [G]; positivity)
  have hgrowth : ∀ m : ℕ, |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ G * m := by
    intro m
    by_cases hm : 2 ≤ m
    · have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
      have hlog : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hmR
      calc
        _ ≤ C₁ * m / Real.log (m : ℝ) := by simpa only [Real.rpow_one] using hb₁ m hm
        _ ≤ C₁ * m / Real.log 2 := div_le_div_of_nonneg_left (by positivity) hl2 hlog
        _ ≤ G * m := by
          have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (C₁ / Real.log 2)) (Nat.cast_nonneg m)
          convert hh using 1 <;> ring
    · have hm01 : m = 0 ∨ m = 1 := by omega
      rcases hm01 with rfl | rfl
      · simp
      · simpa [G] using (le_max_left 1 (C₁ / Real.log 2))
  intro A hA
  obtain ⟨K, hK, hk⟩ := LeanLab.PNTPort.BV.log_rpow_le_sqrt A
  obtain ⟨C, hC, hb⟩ := hPNTpoint A hA
  let B := G * K + C * (2 : ℝ) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have huniform : ∀ Y : ℝ, 2 ≤ Y → ∀ m : ℕ, (m : ℝ) ≤ Y →
      |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ B * Y / Real.log Y ^ A := by
    intro Y hY m hmY
    have hY0 : 0 < Y := by linarith
    have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
    have hlogpow : 0 < Real.log Y ^ A := Real.rpow_pos_of_pos hlogY A
    have hs0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
    have hs2 : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
    by_cases hmS : (m : ℝ) ≤ Real.sqrt Y
    · calc
        _ ≤ G * m := hgrowth m
        _ ≤ G * Real.sqrt Y := mul_le_mul_of_nonneg_left hmS hG
        _ ≤ G * K * Y / Real.log Y ^ A := by
          apply (le_div_iff₀ hlogpow).2
          have hh := mul_le_mul_of_nonneg_left (hk Y hY) (mul_nonneg hG hs0)
          calc
            _ ≤ G * Real.sqrt Y * (K * Real.sqrt Y) := hh
            _ = G * K * (Real.sqrt Y ^ 2) := by ring
            _ = _ := by rw [hs2]
        _ ≤ B * Y / Real.log Y ^ A := by
          apply div_le_div_of_nonneg_right _ hlogpow.le
          apply mul_le_mul_of_nonneg_right _ hY0.le
          dsimp [B]
          have h₁ : 0 ≤ G * K := by positivity
          have h₂ : 0 ≤ C * (2 : ℝ) ^ A := by positivity
          linarith
    · have hs1 : 1 ≤ Real.sqrt Y := by nlinarith only [hs2, hs0, hY]
      have hm2 : 2 ≤ m := by
        have hm1 : (1 : ℝ) < m := by linarith
        exact_mod_cast hm1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
      have hhalf : Real.log Y / 2 ≤ Real.log (m : ℝ) := by
        have hh := Real.log_le_log (Real.sqrt_pos.mpr hY0) (le_of_not_ge hmS)
        simpa only [Real.log_sqrt hY0.le] using hh
      have hhalf0 : 0 < Real.log Y / 2 := by positivity
      have hp : (Real.log Y / 2) ^ A ≤ Real.log (m : ℝ) ^ A :=
        Real.rpow_le_rpow hhalf0.le hhalf hA.le
      calc
        _ ≤ C * m / Real.log (m : ℝ) ^ A := hb m hm2
        _ ≤ C * m / (Real.log Y / 2) ^ A :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hhalf0 A) hp
        _ ≤ C * Y / (Real.log Y / 2) ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmY hC) (Real.rpow_nonneg hhalf0.le A)
        _ = (C * (2 : ℝ) ^ A) * Y / Real.log Y ^ A := by
          rw [Real.div_rpow hlogY.le (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp
        _ ≤ B * Y / Real.log Y ^ A := by
          apply div_le_div_of_nonneg_right _ hlogpow.le
          apply mul_le_mul_of_nonneg_right _ hY0.le
          dsimp [B]
          have h₁ : 0 ≤ G * K := by positivity
          have h₂ : 0 ≤ C * (2 : ℝ) ^ A := by positivity
          linarith
  refine ⟨2 * B, by positivity, fun X hX m hm => ?_⟩
  have hX0 : 0 < X := by linarith
  have hm2X : (m : ℝ) ≤ 2 * X := by
    have hh : (m : ℝ) ≤ (⌊X⌋₊ : ℕ) + (1 : ℝ) := by exact_mod_cast hm
    have hf := Nat.floor_le hX0.le
    linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  calc
    _ ≤ B * (2 * X) / Real.log (2 * X) ^ A := huniform (2 * X) (by linarith) m hm2X
    _ ≤ B * (2 * X) / Real.log X ^ A :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlogX A)
        (Real.rpow_le_rpow hlogX.le (Real.log_le_log hX0 (by linarith)) hA.le)
    _ = _ := by ring


/-- Page 7 PNT step. Endpoint correction from the exact strong PNT bound.
CONDITIONAL ON the supplied strong PNT input. -/
theorem pointwise_pnt_of_strong221
    (hStrong : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      |∑ i ∈ Finset.range m, (Λ i - 1)| ≤ C * m / Real.log (m : ℝ) ^ A := by
  obtain ⟨c, hc, K, hp⟩ := hStrong
  let K₀ := max K 0
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  intro A hA
  obtain ⟨Ke, hKe, he⟩ := LeanLab.PNTPort.BV.exp_neg_sqrt_log_le c hc A
  obtain ⟨Kl, hKl, hl⟩ := LeanLab.PNTPort.BV.log_rpow_le_rpow (A + 1) 1 (by norm_num)
  refine ⟨K₀ * Ke + Kl, by positivity, fun m hm => ?_⟩
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hpow : 0 < Real.log (m : ℝ) ^ A := Real.rpow_pos_of_pos hlog A
  have hψ : Chebyshev.psi (m : ℝ) = (∑ i ∈ Finset.range m, Λ i) + Λ m := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    have hs : Finset.Icc 0 m = Finset.range (m + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [hs, Finset.sum_range_succ]
  have herr : (∑ i ∈ Finset.range m, (Λ i - 1)) =
      (Chebyshev.psi (m : ℝ) - m) - Λ m := by
    rw [hψ, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  have hψb : |Chebyshev.psi (m : ℝ) - m| ≤ (K₀ * Ke) * m / Real.log (m : ℝ) ^ A := by
    calc
      _ ≤ K * m * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := hp m hmR
      _ ≤ K₀ * m * Real.exp (-c * Real.sqrt (Real.log (m : ℝ))) := by
        gcongr
        exact le_max_left _ _
      _ ≤ K₀ * m * (Ke / Real.log (m : ℝ) ^ A) :=
        mul_le_mul_of_nonneg_left (he m hmR) (by positivity)
      _ = _ := by ring
  have hlogb : Real.log (m : ℝ) ≤ Kl * m / Real.log (m : ℝ) ^ A := by
    apply (le_div_iff₀ hpow).2
    have hh := hl (m : ℝ) hmR
    rw [Real.rpow_add hlog, Real.rpow_one, Real.rpow_one] at hh
    nlinarith only [hh]
  have hΛ : |Λ m| ≤ Real.log (m : ℝ) := by
    simpa only [Real.norm_eq_abs] using vonMangoldt_le_log_scale221 hmR (le_refl (m : ℝ))
  rw [herr]
  calc
    _ ≤ |Chebyshev.psi (m : ℝ) - m| + |Λ m| := abs_sub _ _
    _ ≤ (K₀ * Ke) * m / Real.log (m : ℝ) ^ A + Kl * m / Real.log (m : ℝ) ^ A :=
      add_le_add hψb (hΛ.trans hlogb)
    _ = _ := by ring

/-- LEAF. Page 8 equation 9 (part 1).
The base case k = 0 follows from Theorem 3.1. -/
theorem thm1_1_base_case_k0 (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 6) : LevelGP θ := by
  exact akeno_thm1_1 θ hθ0 hθ1

/-
RETIRED 2026-10-31 by the architect, run 20261031T2235Z-16111, ONE-TIME STATEMENT FIX. The two
leaves below are kept as text, not as declarations. Neither is used by the assembly.
`thm1_1_triangle_bound` had no hypotheses and dropped the paper's implied constant; it is false,
proved in `LeanLab.Common.FalseLeafAudit20261031b.thm1_1_triangle_bound_old_false`.
`thm1_1_cauchy_schwarz` used the natural number exponent `1/2 = 0`, so it said only
`levelSum ≤ 1`, see `thm1_1_cauchy_schwarz_old_is_le_one` there.
`thm1_1_base_case_k0` now takes the range `0 < θ < 1/6` of Theorem 1.1, which the assembly has.

/ -- LEAF. Page 8 equation 9 (part 2).
The triangle inequality bound `Σ_{d} R_{d,l}(N) ≪ (ln X)^2`. - /
theorem thm1_1_triangle_bound (θ : ℝ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ) :
    ‖Rdl w₁ w₂ X N d l‖ ≤ X / d * Real.log X ^ 2 := RETIRED, no proof term

/ -- LEAF. Page 8 equation 9 (part 3).
Cauchy-Schwarz inequality application to reduce the k-th moment to the 0-th moment. - /
theorem thm1_1_cauchy_schwarz (θ : ℝ) (k : ℕ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N : ℕ) :
    levelSum θ k w₁ w₂ X N ≤
      (X * Real.log X ^ 2) ^ (1/2) * (levelSum θ 0 w₁ w₂ X N) ^ (1/2) := RETIRED, no proof term

-/

/-- LEAF. Page 8 equation 9 (part 4).
The final step of the reduction from k > 0 to k = 0. -/
theorem thm1_1_reduction_to_k0 (θ : ℝ) (hk0 : LevelGP θ) : LevelGP θ := hk0

/-- The exact sealed cited Prop for Theorem 1.1, assembled from the leaf with no sorry in this proof.
Uses the cited akeno_thm3_1 through the base case leaf. -/
theorem akeno_thm1_1_assembled : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ := by
  intro θ hθ0 hθ1
  exact thm1_1_reduction_to_k0 θ (thm1_1_base_case_k0 θ hθ0 hθ1)

end LeanLab.Akeno2026.DecompJ267
