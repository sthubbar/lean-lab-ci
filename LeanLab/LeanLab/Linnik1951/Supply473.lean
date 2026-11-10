/-
P0093 page 159 before equation 5.1. Prime power series bookkeeping.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SecondMoment111

open scoped Topology
open Complex Filter

namespace LeanLab.Linnik1951

/-- Positive prime powers have unique prime and exponent indices. This is the
reindexing used for the absolute convergence before equation 5.1 on page 159. -/
theorem prime_power_index_injective473 :
    Function.Injective (fun x : Nat.Primes × ℕ => (x.1 : ℕ) ^ (x.2 + 1)) := by
  intro x y h
  obtain ⟨hp, hm⟩ := x.1.property.pow_inj y.1.property h
  exact Prod.ext (Subtype.ext hp) hm

/-- P0093 page 159 before equation 5.1. Exponential damping is summable on
all positive prime powers, with each prime power appearing once. -/
theorem prime_power_damping_summable473 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun x : Nat.Primes × ℕ =>
      Real.exp (-(((x.1 : ℕ) : ℝ) ^ (x.2 + 1) / (N : ℝ)))) := by
  simpa only [Function.comp_def, Nat.cast_pow, neg_div] using
    (damping_summable111 N hN).comp_injective prime_power_index_injective473

/-- P0093 page 159 equation 5.1 audit. Summability of the analytic logarithms
inside the unit disk forces summability of their inputs. -/
theorem summable_of_summable_neg_log473 {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ < 1)
    (hs : Summable (fun i => -Complex.log (1 - z i))) : Summable z := by
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - Complex.exp (-w)) 0 := by fun_prop
  have ho : (fun w : ℂ => 1 - Complex.exp (-w)) =O[𝓝 0] id := by
    simpa only [neg_zero, Complex.exp_zero, sub_self, sub_zero] using! hd.isBigO_sub
  have h := ho.comp_summable hs
  convert h using 1
  funext i
  have hne : 1 - z i ≠ 0 := by
    intro he
    have heq : z i = 1 := (sub_eq_zero.mp he).symm
    have := hz i
    simp [heq] at this
  simp [Complex.exp_log hne]

/-- P0093 page 159 equation 5.1 audit. For positive real part the inner
prime power series equals the negative logarithm of its Euler factor. -/
theorem prime_power_log_series473 (s : ℂ) (hs : 0 < s.re) (p : Nat.Primes) :
    ∑' m : ℕ, ((m : ℂ) + 1)⁻¹ * (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)
      = -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hz : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  convert (Complex.hasSum_taylorSeries_neg_log' hz).tsum_eq using 1
  apply tsum_congr
  intro m
  rw [← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
  ring

/-- P0093 page 159 equation 5.1 audit. An unordered prime Dirichlet series
cannot converge when the real part is at most one. -/
theorem prime_cpow_not_summable473 (s : ℂ) (hs : s.re ≤ 1) :
    ¬ Summable (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s)) := by
  intro h
  have hn := h.norm
  have hr : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s.re)) := by
    convert hn using 1
    funext p
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos]
    · rfl
    · exact_mod_cast p.property.pos
  have := Nat.Primes.summable_rpow.mp hr
  linarith

/-- P0093 page 159 equation 5.1 audit. The iterated unordered prime power
series is zero by the tsum convention in the critical strip. -/
theorem prime_power_undamped_tsum_zero473 (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) :
    (∑' p : Nat.Primes, ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)) = 0 := by
  simp_rw [prime_power_log_series473 s hs0]
  apply tsum_eq_zero_of_not_summable
  intro h
  apply prime_cpow_not_summable473 s hs1
  apply summable_of_summable_neg_log473 _ _ h
  intro p
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)

/-- P0093 page 159 equation 5.1 annotation audit. For every character the unordered prime Dirichlet series is not summable
when the real part is at most one. Only finitely many primes divide the modulus. -/
theorem character_prime_cpow_not_summable473 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : s.re ≤ 1) :
    ¬ Summable (fun p : Nat.Primes => χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) := by
  intro h
  have hf : {p : Nat.Primes | (p : ℕ) ≤ q}.Finite :=
    Set.Finite.preimage Nat.Primes.coe_nat_injective.injOn (Set.finite_Iic q)
  have he : ∀ᶠ p : Nat.Primes in cofinite, ‖χ (p : ℕ)‖ = 1 := by
    filter_upwards [hf.compl_mem_cofinite] with p hp
    have hqp : q < (p : ℕ) := by simpa using hp
    have hu : IsUnit ((p : ℕ) : ZMod q) :=
      (ZMod.isUnit_prime_iff_not_dvd p.property).mpr
        (Nat.not_dvd_of_pos_of_lt (NeZero.pos q) hqp)
    simpa only [IsUnit.unit_spec] using χ.unit_norm_eq_one hu.unit
  have hn : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s.re)) := by
    apply h.norm.congr_cofinite
    filter_upwards [he] with p hp
    rw [norm_mul, hp, one_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.property.pos)]
    rfl
  have := Nat.Primes.summable_rpow.mp hn
  linarith

/-- P0093 page 159 equation 5.1 annotation audit. The inner character prime power series is the negative logarithm of its
Euler factor when the real part is positive. -/
theorem character_prime_power_log_series473 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 0 < s.re) (p : Nat.Primes) :
    ∑' m : ℕ, ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)
      = -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hz0 : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hz : ‖χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)) hz0
  convert (Complex.hasSum_taylorSeries_neg_log' hz).tsum_eq using 1
  apply tsum_congr
  intro m
  rw [mul_pow, ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul, map_pow]
  ring

/-- P0093 page 159 equation 5.1 annotation audit. Every character has zero
unordered prime power tsum in the open critical strip. -/
theorem character_prime_power_undamped_zero473 (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) :
    (∑' p : Nat.Primes, ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)) = 0 := by
  simp_rw [character_prime_power_log_series473 q χ s hs0]
  apply tsum_eq_zero_of_not_summable
  intro h
  apply character_prime_cpow_not_summable473 q χ s hs1
  apply summable_of_summable_neg_log473 _ _ h
  intro p
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hz : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)) hz

/-- P0093 page 159 equation 5.1 annotation audit. On every vertical line a
nonprincipal L-function has a point whose principal complex logarithm is nonzero. -/
theorem log_L_nonzero_on_vertical473 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℝ) :
    ∃ t : ℝ, Complex.log (DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  by_contra! hall
  let g : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * Complex.I
  have hg : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝[≠] (σ : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous g := by fun_prop
      have hc0 : Tendsto g (𝓝 (0 : ℝ)) (𝓝 (g 0)) := hc.continuousAt
      simpa only [g, Complex.ofReal_zero, zero_mul, add_zero] using! hc0.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro he
      apply ht
      have hi := congrArg Complex.im he
      simpa [g] using hi
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (σ : ℂ),
      DirichletCharacter.LFunction χ z = 0 ∨ DirichletCharacter.LFunction χ z = 1 := by
    apply hg.frequently
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro t
    by_cases hz : DirichletCharacter.LFunction χ (g t) = 0
    · exact Or.inl hz
    · apply Or.inr
      have h := Complex.exp_log hz
      rw [show Complex.log (DirichletCharacter.LFunction χ (g t)) = 0 from hall t,
        Complex.exp_zero] at h
      exact h.symm
  rcases frequently_or_distrib.mp hfreq with hz | ho
  · have heq := hf.eq_of_frequently_eq analyticOnNhd_const hz
    exact (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (s := 2) (by norm_num))
      (congrFun heq 2)
  have heq := hf.eq_of_frequently_eq analyticOnNhd_const ho
  rcases χ.even_or_odd with he | ho
  · have hz : DirichletCharacter.LFunction χ (-2) = 0 := by
      simpa using he.LFunction_neg_two_mul_nat_add_one 0
    have h := congrFun heq (-2)
    rw [hz] at h
    norm_num at h
  · have hz : DirichletCharacter.LFunction χ (-1) = 0 := by
      simpa using ho.LFunction_neg_two_mul_nat_sub_one 0
    have h := congrFun heq (-1)
    rw [hz] at h
    norm_num at h

/-- P0093 page 159 equation 5.1 supply. To the right of one the undamped
prime power series is absolutely summable. This is the starting contour range. -/
theorem prime_power_undamped_summable473 (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun x : Nat.Primes × ℕ =>
      ‖((x.2 : ℂ) + 1)⁻¹ * χ ((x.1 : ℕ) ^ (x.2 + 1)) *
        (((x.1 : ℕ) : ℂ) ^ (x.2 + 1)) ^ (-s)‖) := by
  have hsum : Summable (fun n : ℕ => ‖(n : ℂ) ^ (-s)‖) :=
    summable_riemannZetaSummand hs
  apply Summable.of_nonneg_of_le (fun x => norm_nonneg _) _ (hsum.comp_injective prime_power_index_injective473)
  intro x
  simp only [Function.comp_def, Nat.cast_pow]
  rw [norm_mul, norm_mul, norm_inv]
  have hcast : (x.2 : ℂ) + 1 = (((x.2 : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcoeff : ((x.2 : ℝ) + 1)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) x.2]
  have hc : ‖χ ((x.1 : ℕ) ^ (x.2 + 1))‖ ≤ 1 :=
    DirichletCharacter.norm_le_one _ _
  calc
    _ ≤ 1 * 1 * ‖(((x.1 : ℕ) : ℂ) ^ (x.2 + 1)) ^ (-s)‖ := by gcongr
    _ = _ := by ring

/-- P0093 page 159 equation 5.1 supply. In the absolute convergence half plane
the exponential of the prime power logarithm series equals the L-function.
The conclusion avoids choosing an invalid principal logarithm branch. -/
theorem exp_prime_power_eq_LFunction473 (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)) = DirichletCharacter.LFunction χ s := by
  simp_rw [character_prime_power_log_series473 q χ s (by linarith)]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_eulerProduct_exp_log hs

end LeanLab.Linnik1951
