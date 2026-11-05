import LeanLab.ChenDoubleSieve.Decomp363f

/-!
An explicit dimension bound for the odd prime interval product in Wu 2004.
The Mertens block estimate already proved in task101 is reused unchanged.
The endpoint convention is natural y exclusive and w inclusive.
Source: https://arxiv.org/pdf/0705.1652, page 5 equation 2.3 and page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363
open LeanLab.ChenPrimeExceptional.Task101
open LeanLab.PNTSieve.Mertens

/-- The shifted Euler logarithm differs from minus one over p by at most ten over p squared. -/
theorem shifted_factor_log_error {p : ℕ} (hp : 3 ≤ p) :
    |log (1 - 1 / ((p : ℝ) - 1)) + 1 / (p : ℝ)| ≤ 10 / (p : ℝ) ^ 2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm : 0 < (p : ℝ) - 1 := by linarith
  have hbase := euler_log_error (p := p - 1) (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at hbase
  have hrecip : 1 / ((p : ℝ) - 1) ≤ 2 / p := by
    rw [div_le_div_iff₀ hpm hp0]
    linarith
  have hdiff : 0 ≤ 1 / ((p : ℝ) - 1) - 1 / p := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hpm (by linarith))
  have hdiff2 : 1 / ((p : ℝ) - 1) - 1 / p ≤ 2 / (p : ℝ) ^ 2 := by
    have he : 1 / ((p : ℝ) - 1) - 1 / p = 1 / (((p : ℝ) - 1) * p) := by
      field_simp; ring
    rw [he, div_le_div_iff₀ (mul_pos hpm hp0) (sq_pos_of_pos hp0)]
    nlinarith
  have hsq : 2 * (1 / ((p : ℝ) - 1)) ^ 2 ≤ 8 / (p : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * (2 / (p : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring
  have htri := abs_add_le
    (log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1))
    (-(1 / ((p : ℝ) - 1) - 1 / p))
  simp only [abs_neg, abs_of_nonneg hdiff] at htri
  have he : log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1) +
      -(1 / ((p : ℝ) - 1) - 1 / p) = log (1 - 1 / ((p : ℝ) - 1)) + 1 / p := by ring
  rw [he] at htri
  calc
    _ ≤ 8 / (p : ℝ) ^ 2 + 2 / (p : ℝ) ^ 2 :=
      htri.trans (add_le_add (hbase.trans hsq) hdiff2)
    _ = _ := by ring



/-- The odd prime Euler block on the natural interval from y exclusive to w inclusive. -/
def oddEulerBlock (y w : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ioc y w).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1))

/-- Every odd prime interval product above two is positive. -/
theorem oddEulerBlock_pos {y w : ℕ} (hy : 2 ≤ y) : 0 < oddEulerBlock y w := by
  apply Finset.prod_pos
  intro p hp
  have hpR : (3 : ℝ) ≤ p := by
    have hpy := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    exact_mod_cast (show 3 ≤ p by omega)
  have hi : 1 / ((p : ℝ) - 1) < 1 :=
    (div_lt_one (by linarith)).2 (by linarith)
  linarith

/-- The shifted product logarithm has an explicit reciprocal sum error at most ten over y. -/
theorem oddEulerBlock_log_error {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    |log (oddEulerBlock y w) + (E w - E y)| ≤ 10 / (y : ℝ) := by
  have hpos : ∀ p ∈ (Finset.Ioc y w).filter Nat.Prime,
      0 < 1 - 1 / ((p : ℝ) - 1) := by
    intro p hp
    have hpR : (3 : ℝ) ≤ p := by
      have hpy := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      exact_mod_cast (show 3 ≤ p by omega)
    have hi : 1 / ((p : ℝ) - 1) < 1 :=
      (div_lt_one (by linarith)).2 (by linarith)
    linarith
  rw [oddEulerBlock, log_prod (fun p hp => (hpos p hp).ne'),
    ← reciprocal_block_eq hyw, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ p ∈ (Finset.Ioc y w).filter Nat.Prime,
        |log (1 - 1 / ((p : ℝ) - 1)) + 1 / (p : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Finset.Ioc y w).filter Nat.Prime, 10 / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpy := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      exact shifted_factor_log_error (by omega)
    _ ≤ ∑ p ∈ Finset.Ioc y w, 10 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = 10 * ∑ p ∈ Finset.Ioc y w, ((p : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [div_eq_mul_inv]
    _ ≤ 10 * ((y : ℝ)⁻¹ - (w : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (by omega : y ≠ 0) hyw) (by norm_num)
    _ ≤ _ := by
      have hw : 0 ≤ (w : ℝ)⁻¹ := by positivity
      simp only [div_eq_mul_inv]
      linarith

/-- The odd Euler product logarithm differs from its Mertens ratio logarithm by the stated error. -/
theorem oddEulerBlock_log_ratio_error {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    |log (oddEulerBlock y w) - log (log y / log w)| ≤
      22 / log y + 10 / (y : ℝ) := by
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hwR : (1 : ℝ) < w := by exact_mod_cast (show 1 < w by omega)
  rw [log_div (log_pos hyR).ne' (log_pos hwR).ne']
  have h1 := oddEulerBlock_log_error hy hyw
  have h2 := reciprocal_block_error hy hyw
  have he : log (oddEulerBlock y w) - (log (log y) - log (log w)) =
      (log (oddEulerBlock y w) + (E w - E y)) -
        (E w - E y - (log (log w) - log (log y))) := by ring
  rw [he]
  have ht := abs_sub (log (oddEulerBlock y w) + (E w - E y))
    (E w - E y - (log (log w) - log (log y)))
  linarith

/-- Exponentiating the error gives a uniform upper bound for the inverse odd interval product. -/
theorem oddEulerBlock_inv_le {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    1 / oddEulerBlock y w ≤ (log w / log y) * exp (22 / log y + 10 / (y : ℝ)) := by
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hwR : (1 : ℝ) < w := by exact_mod_cast (show 1 < w by omega)
  have hylog := log_pos hyR
  have hwlog := log_pos hwR
  have he : log (log w / log y) = -log (log y / log w) := by
    rw [log_div hwlog.ne' hylog.ne', log_div hylog.ne' hwlog.ne']
    ring
  have hlow := (abs_le.mp (oddEulerBlock_log_ratio_error hy hyw)).1
  have hb : -log (oddEulerBlock y w) ≤ log (log w / log y) + (22 / log y + 10 / (y : ℝ)) := by
    rw [he]
    linarith
  calc
    _ = exp (-log (oddEulerBlock y w)) := by
      rw [exp_neg, exp_log (oddEulerBlock_pos hy), one_div]
    _ ≤ exp (log (log w / log y) + (22 / log y + 10 / (y : ℝ))) := exp_le_exp.mpr hb
    _ = _ := by rw [exp_add, exp_log (div_pos hwlog hylog)]


/-- The natural endpoint odd Euler product satisfies the dimension one logarithmic bound. The constant is absolute and exceeds one. -/
theorem oddEulerBlock_dimension : ∃ K : ℝ, 1 < K ∧ ∀ y w : ℕ,
    2 ≤ y → y ≤ w → 1 / oddEulerBlock y w ≤
      (log w / log y) * (1 + K / log y) := by
  let M : ℝ := 32 / log 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : 1 < 32 * exp M := by nlinarith [Real.one_le_exp hM]
  refine ⟨32 * exp M, hK, ?_⟩
  intro y w hy hyw
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hwR : (1 : ℝ) < w := by exact_mod_cast (show 1 < w by omega)
  have hy0 : (0 : ℝ) < y := by linarith
  have hly : 0 < log (y : ℝ) := log_pos hyR
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2 : log (2 : ℝ) ≤ log y := log_le_log (by norm_num) (by exact_mod_cast hy)
  have hlogy : log (y : ℝ) ≤ y := by linarith [log_le_sub_one_of_pos hy0]
  have hE : 22 / log (y : ℝ) + 10 / (y : ℝ) ≤ 32 / log y := by
    have hb : 10 / (y : ℝ) ≤ 10 / log y := div_le_div_of_nonneg_left (by norm_num) hly hlogy
    calc _ ≤ 22 / log (y : ℝ) + 10 / log y := add_le_add le_rfl hb
         _ = _ := by ring
  let t : ℝ := 32 / log y
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htM : t ≤ M := div_le_div_of_nonneg_left (by norm_num) hl2 hlog2
  have hexp : exp t ≤ 1 + t * exp M := by
    have h := add_one_le_exp (-t)
    have hh := mul_le_mul_of_nonneg_right h (exp_pos t).le
    have he : exp (-t) * exp t = 1 := by rw [← exp_add]; simp
    rw [he] at hh
    have hcomp : t * exp t ≤ t * exp M := mul_le_mul_of_nonneg_left (exp_le_exp.mpr htM) ht
    nlinarith
  have hratio : 0 ≤ log (w : ℝ) / log y := div_nonneg (log_pos hwR).le hly.le
  calc
    _ ≤ (log w / log y) * exp (22 / log y + 10 / (y : ℝ)) := oddEulerBlock_inv_le hy hyw
    _ ≤ (log w / log y) * exp t := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hE) hratio
    _ ≤ (log w / log y) * (1 + t * exp M) := mul_le_mul_of_nonneg_left hexp hratio
    _ = _ := by dsimp [t]; ring

/-- A strict real prime interval with natural successor endpoints is the usual
natural open closed interval of primes. -/
theorem PS_nat_successors (y w : ℕ) :
    Wu41.PS 1 ((y : ℝ) + 1) ((w : ℝ) + 1) =
      (Finset.Ioc y w).filter Nat.Prime := by
  ext p
  simp only [Wu41.mem_PS, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hp, hpy, hpw, _⟩
    have hpyN : y + 1 ≤ p := by exact_mod_cast hpy
    have hpwN : p < w + 1 := by exact_mod_cast hpw
    exact ⟨⟨by omega, by omega⟩, hp⟩
  · rintro ⟨⟨hpy, hpw⟩, hp⟩
    refine ⟨hp, ?_, ?_, by simp⟩
    · exact_mod_cast (show y + 1 ≤ p by omega)
    · exact_mod_cast (show p < w + 1 by omega)

/-- The actual local densities obey the uniform dimension bound at natural
successor cutoffs. The displayed logarithms retain the predecessor endpoints. -/
theorem localDensity_nat_dimension : ∃ K : ℝ, 1 < K ∧ ∀ N : ℕ,
    Even N → ∀ y w : ℕ, 2 ≤ y → y ≤ w →
      localDensity N ((y : ℝ) + 1) / localDensity N ((w : ℝ) + 1) ≤
        (log w / log y) * (1 + K / log y) := by
  obtain ⟨K, hK, hbound⟩ := oddEulerBlock_dimension
  refine ⟨K, hK, ?_⟩
  intro N hEven y w hy hyw
  have hw : (3 : ℝ) ≤ (y : ℝ) + 1 := by exact_mod_cast (show 3 ≤ y + 1 by omega)
  have horder : (y : ℝ) + 1 ≤ (w : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ hyw)
  have hcmp := localDensity_ratio_le hEven hw horder
  calc
    _ ≤ 1 / oddEulerBlock y w := by
      simpa only [PS_nat_successors, Finset.prod_inv_distrib, oddEulerBlock, one_div] using hcmp
    _ ≤ _ := hbound y w hy hyw

end LeanLab.ChenDoubleSieve.Task363
