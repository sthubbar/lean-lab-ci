/-
P0069, Section 3, pages 11 to 15. Finer leaves for the mean value
input used by the sieve decomposition in DecompC165b.
Every analytic leaf is OPEN. The exact final assembly is CONDITIONAL.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165
import LeanLab.BHP1997.Decomp513a
import LeanLab.BHP1997.Thm4Exponents
import LeanLab.Akeno2026.Decomp86
import LeanLab.BHP1997.EnergyLogC165

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- Pages 11 and 12. The multiplicative character weight in each Dirichlet term. -/
noncomputable def characterWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℕ →* ℂ where
  toFun n := χ (n : ZMod q) / (n : ℂ) ^ s
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
    exact mul_div_mul_comm _ _ _ _
/-- Pages 11 and 12. The coefficient sequence truncated to the actual polynomial support.
Multiplication in the Mathlib monoid algebra is finite Dirichlet convolution. -/
noncomputable def truncatedCoeffs (a : ℕ → ℂ) (c1 c2 F : ℝ) : MonoidAlgebra ℂ ℕ :=
  ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F), MonoidAlgebra.single n (a n)
/-- Page 12, the polynomial is evaluation of its truncated coefficient algebra. -/
theorem dirPoly_eq_lift (a : ℕ → ℂ) (c1 c2 F : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Thm4.dirPoly a c1 c2 F χ s =
      MonoidAlgebra.lift ℂ ℂ ℕ (characterWeight χ s) (truncatedCoeffs a c1 c2 F) := by
  classical
  simp [truncatedCoeffs, Thm4.dirPoly, characterWeight, mul_div_assoc]

/-- Page 12, "using (3.1) to bound G(P^g) by 𝓛^B". A divisor bound on coefficients gives a log
power bound on the coefficient energy, uniformly in the sequence. -/
def EnergyLogBound : Prop :=
  ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K C : ℝ, 0 < C ∧
    ∀ a : ℕ → ℂ, Thm4.CoeffBound a B → ∀ F : ℝ, 2 ≤ F →
      energy a c1 c2 F ≤ C * Real.log F ^ K

/-- Page 12, the standard divisor moment behind "using (3.1) to bound G(P^g) by 𝓛^B".
P0069 Baker Harman Pintz 1997, Section 3, proof of Theorem 4, page 12.
For every real exponent k the k-th divisor moment up to N is at most a constant times
N times a fixed power of 1 + log N. The paper uses it without a written derivation.
PROVED, ROUTE BURST 2, formerly LEAF, OPEN: from `τ ≥ 1`, `k ≤ ⌈k⌉`, `n ≤ N` and the harmonic
divisor moment bound `EnergyLogC165.harmonicDivisorMoment_le`, with `K = 2^⌈k⌉` and `C = 1`. -/
theorem divisor_power_moment (k : ℝ) : ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧
    ∀ N : ℕ, (∑ n ∈ Finset.Ioc 0 N, ((n.divisors.card : ℕ) : ℝ) ^ k) ≤
      C * N * (1 + Real.log N) ^ K := by
  set m : ℕ := ⌈k⌉₊
  refine ⟨((2 ^ m : ℕ) : ℝ), 1, by positivity, one_pos, ?_⟩
  intro N
  rw [Real.rpow_natCast, one_mul]
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := Finset.val_inj.mp rfl
  have hterm : ∀ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ k ≤
      (N : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hτ : (1 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    have hk : ((n.divisors.card : ℕ) : ℝ) ^ k ≤ ((n.divisors.card : ℕ) : ℝ) ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hτ (Nat.le_ceil k)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
    have hpos : 0 ≤ ((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ) := by positivity
    calc ((n.divisors.card : ℕ) : ℝ) ^ k ≤ ((n.divisors.card : ℕ) : ℝ) ^ m := hk
      _ = (n : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) := by field_simp
      _ ≤ (N : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hnN hpos
  rw [hIoc]
  calc (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ k)
      ≤ ∑ n ∈ Finset.Icc 1 N, (N : ℝ) * (((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) * EnergyLogC165.harmonicDivisorMoment m N := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ (N : ℝ) * (1 + Real.log N) ^ (2 ^ m) :=
        mul_le_mul_of_nonneg_left (EnergyLogC165.harmonicDivisorMoment_le m N) (Nat.cast_nonneg N)

/-- Page 12, the step "using (3.1)" itself. P0069 Baker Harman Pintz 1997, Section 3,
proof of Theorem 4, page 12, with display 3.1 and the energy G of display 3.3 on page 11.
On the support c1 F < n the weight 1/n is at most 1/(c1 F), and 3.1 bounds the square of the
coefficient by the divisor function to the power 2B. -/
theorem energy_le_divisor_moment {a : ℕ → ℂ} {B c1 c2 F : ℝ}
    (ha : Thm4.CoeffBound a B) (hc1 : 0 < c1) (hF : 0 < F) :
    energy a c1 c2 F ≤
      (∑ n ∈ Finset.Ioc 0 ⌊c2 * F⌋₊, ((n.divisors.card : ℕ) : ℝ) ^ (2 * B)) / (c1 * F) := by
  set N := ⌊c2 * F⌋₊
  set S := (Finset.range (N + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  have hden : 0 < c1 * F := mul_pos hc1 hF
  have hsub : S ⊆ Finset.Ioc 0 N := by
    intro n hn
    obtain ⟨hnN, hnlo, _⟩ := Finset.mem_filter.mp hn
    have hn0 : 0 < (n : ℝ) := hden.trans hnlo
    rw [Finset.mem_range] at hnN
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hn0, by omega⟩
  change (∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ)) ≤ _
  calc
    _ ≤ ∑ n ∈ S, ((n.divisors.card : ℕ) : ℝ) ^ (2 * B) / (c1 * F) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlo := (Finset.mem_filter.mp hn).2.1
      have hsq : ‖a n‖ ^ 2 ≤ ((n.divisors.card : ℕ) : ℝ) ^ (2 * B) := by
        calc
          _ ≤ (((n.divisors.card : ℕ) : ℝ) ^ B) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (ha n) 2
          _ = ((n.divisors.card : ℕ) : ℝ) ^ (B * (2 : ℕ)) :=
            (Real.rpow_mul_natCast (by positivity) B 2).symm
          _ = _ := by congr 1; push_cast; ring
      exact (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)).trans
        (div_le_div_of_nonneg_left (by positivity) hden hnlo.le)
    _ = (∑ n ∈ S, ((n.divisors.card : ℕ) : ℝ) ^ (2 * B)) / (c1 * F) := by
      rw [Finset.sum_div]
    _ ≤ _ :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)) hden.le

/-- Page 12, the logarithmic rescaling in "bound G(P^g) by 𝓛^B". P0069 Baker Harman Pintz 1997,
Section 3, proof of Theorem 4, page 12. With N the integer part of c2 F and F at least 2,
1 + log N is at most a constant depending on c2 times log F. -/
theorem one_add_log_floor_le {c2 F : ℝ} (hc2 : 0 < c2) (hF : 2 ≤ F) :
    1 + Real.log (⌊c2 * F⌋₊ : ℕ) ≤ ((1 + |Real.log c2|) / Real.log 2 + 1) * Real.log F := by
  have hF0 : 0 < F := by linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log F := Real.log_le_log (by norm_num) hF
  have hlogF : 0 ≤ Real.log F := hl2.le.trans hlog
  have hlogN : Real.log ((⌊c2 * F⌋₊ : ℕ) : ℝ) ≤ |Real.log c2| + Real.log F := by
    rcases Nat.eq_zero_or_pos ⌊c2 * F⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    · have hN0 : 0 < ((⌊c2 * F⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpos
      have hNle : ((⌊c2 * F⌋₊ : ℕ) : ℝ) ≤ c2 * F := Nat.floor_le (mul_pos hc2 hF0).le
      have hh := Real.log_le_log hN0 hNle
      rw [Real.log_mul (ne_of_gt hc2) (ne_of_gt hF0)] at hh
      linarith [le_abs_self (Real.log c2)]
  have hscale := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (1 + |Real.log c2|) / Real.log 2 by positivity)
  have hid : (1 + |Real.log c2|) / Real.log 2 * Real.log 2 = 1 + |Real.log c2| :=
    div_mul_cancel₀ _ (ne_of_gt hl2)
  rw [hid] at hscale
  nlinarith

/-- Page 12, the coefficient input cut out of `dyadic_mean_value` by U-1609. It is a
divisor moment bound, `Σ_{n ≤ F} τ(n)^{2B}/n ≪ (log F)^K`, elementary and not in Mathlib. It is
exactly what the bound `energy_small_power` cannot give, see `positive_power_not_log_bounded`.
Burst 2 split: no direct sorry, and no sorry below it: `divisor_power_moment` is now PROVED, through the
proved steps `energy_le_divisor_moment` and `one_add_log_floor_le`. -/
theorem energy_log_bound : EnergyLogBound := by
  intro B c1 c2 hc1 hc12
  have hc2 : 0 < c2 := hc1.trans hc12
  obtain ⟨K, C, hK, hC, hmom⟩ := divisor_power_moment (2 * B)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  set R : ℝ := (1 + |Real.log c2|) / Real.log 2 + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  refine ⟨K, C * (c2 / c1) * R ^ K, by positivity, ?_⟩
  intro a ha F hF
  have hF0 : 0 < F := by linarith
  have hden : 0 < c1 * F := mul_pos hc1 hF0
  have hNle : ((⌊c2 * F⌋₊ : ℕ) : ℝ) ≤ c2 * F := Nat.floor_le (mul_pos hc2 hF0).le
  have hlog1 : 0 ≤ 1 + Real.log ((⌊c2 * F⌋₊ : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos ⌊c2 * F⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; norm_num
    · have h1 : (1 : ℝ) ≤ ((⌊c2 * F⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpos
      linarith [Real.log_nonneg h1]
  have hlogF : 0 ≤ Real.log F := Real.log_nonneg (by linarith)
  have hpow : (1 + Real.log ((⌊c2 * F⌋₊ : ℕ) : ℝ)) ^ K ≤ R ^ K * Real.log F ^ K := by
    rw [← Real.mul_rpow hR.le hlogF]
    exact Real.rpow_le_rpow hlog1 (one_add_log_floor_le hc2 hF) hK
  calc
    energy a c1 c2 F ≤
        (∑ n ∈ Finset.Ioc 0 ⌊c2 * F⌋₊, ((n.divisors.card : ℕ) : ℝ) ^ (2 * B)) / (c1 * F) :=
      energy_le_divisor_moment ha hc1 hF0
    _ ≤ (C * ((⌊c2 * F⌋₊ : ℕ) : ℝ) * (1 + Real.log ((⌊c2 * F⌋₊ : ℕ) : ℝ)) ^ K) / (c1 * F) :=
      div_le_div_of_nonneg_right (hmom _) hden.le
    _ ≤ (C * (c2 * F) * (R ^ K * Real.log F ^ K)) / (c1 * F) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hNle hC.le) hpow
        (Real.rpow_nonneg hlog1 _) (by positivity)
    _ = C * (c2 / c1) * R ^ K * Real.log F ^ K := by
      field_simp

/-- Page 12, powers are evaluated finite Dirichlet convolutions. -/
theorem dirPoly_pow_eq_lift (a : ℕ → ℂ) (c1 c2 F : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (g : ℕ) :
    Thm4.dirPoly a c1 c2 F χ s ^ g =
      MonoidAlgebra.lift ℂ ℂ ℕ (characterWeight χ s) (truncatedCoeffs a c1 c2 F ^ g) := by
  rw [dirPoly_eq_lift, map_pow]

/-- Pages 11 and 12, truncation preserves precisely the support coefficients. -/
theorem truncatedCoeffs_coeff (a : ℕ → ℂ) (c1 c2 F : ℝ) (n : ℕ) :
    (truncatedCoeffs a c1 c2 F).coeff n =
      if c1 * F < n ∧ (n : ℝ) < c2 * F then a n else 0 := by
  classical
  have hrange (h : (n : ℝ) < c2 * F) : n < ⌊c2 * F⌋₊ + 1 := by
    exact Nat.lt_succ_of_le (Nat.le_floor h.le)
  simp only [truncatedCoeffs, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases h : c1 * F < n ∧ (n : ℝ) < c2 * F
  · simp [h, Finset.mem_filter, Finset.mem_range, hrange h.2]
  · simp [h, Finset.mem_filter]

/-- Page 12, convolution support is multiplicative in its length. -/
theorem coeff_pow_bounds (p : MonoidAlgebra ℂ ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hp : ∀ n ∈ p.coeff.support, lo ≤ n ∧ (n : ℝ) ≤ hi) (g : ℕ) :
    ∀ n ∈ (p ^ g).coeff.support, lo ^ g ≤ n ∧ (n : ℝ) ≤ hi ^ g := by
  classical
  induction g with
  | zero =>
    intro n hn
    have : n = 1 := by simpa [MonoidAlgebra.one_def] using hn
    subst n
    simp
  | succ g ih =>
    intro n hn
    rw [pow_succ] at hn
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp
      (MonoidAlgebra.support_coeff_mul_subset _ _ hn)
    obtain ⟨hu1, hu2⟩ := ih u hu
    obtain ⟨hv1, hv2⟩ := hp v hv
    push_cast
    rw [pow_succ, pow_succ]
    exact ⟨mul_le_mul hu1 hv1 hlo.le (by positivity),
      mul_le_mul hu2 hv2 (hlo.le.trans hv1) (by positivity)⟩

/-- Page 12, positive convolution powers have strict multiplicative support endpoints. -/
theorem coeff_pow_strict_bounds (p : MonoidAlgebra ℂ ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi)
    (hp : ∀ n ∈ p.coeff.support, lo < n ∧ (n : ℝ) < hi) (g : ℕ) (hg : 0 < g) :
    ∀ n ∈ (p ^ g).coeff.support, lo ^ g < n ∧ (n : ℝ) < hi ^ g := by
  classical
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
  intro n hn
  rw [pow_succ] at hn
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp
    (MonoidAlgebra.support_coeff_mul_subset _ _ hn)
  obtain ⟨hu1, hu2⟩ := coeff_pow_bounds p hlo hhi.le
    (fun n hn => ⟨(hp n hn).1.le, (hp n hn).2.le⟩) g u hu
  obtain ⟨hv1, hv2⟩ := hp v hv
  push_cast
  rw [pow_succ, pow_succ]
  constructor
  · calc
      lo ^ g * lo < lo ^ g * v := mul_lt_mul_of_pos_left hv1 (pow_pos hlo _)
      _ ≤ u * v := mul_le_mul_of_nonneg_right hu1 (hlo.le.trans hv1.le)
  · calc
      (u : ℝ) * v ≤ hi ^ g * v := mul_le_mul_of_nonneg_right hu2 (hlo.le.trans hv1.le)
      _ < hi ^ g * hi := mul_lt_mul_of_pos_left hv2 (pow_pos hhi _)

/-- Page 12, a finite convolution with the indicated support is a Dirichlet polynomial. -/
theorem lift_eq_dirPoly (p : MonoidAlgebra ℂ ℕ) (c1 c2 F : ℝ)
    (hp : ∀ n ∈ p.coeff.support, c1 * F < n ∧ (n : ℝ) < c2 * F)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    MonoidAlgebra.lift ℂ ℂ ℕ (characterWeight χ s) p =
      Thm4.dirPoly p.coeff c1 c2 F χ s := by
  classical
  have hsub : p.coeff.support ⊆ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
      (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F) := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.le_floor (hp n hn).2.le)), hp n hn⟩
  rw [MonoidAlgebra.lift_apply', Finsupp.sum_of_support_subset p.coeff hsub]
  · simp [Thm4.dirPoly, characterWeight, mul_div_assoc]
  · intro n hn; simp

/-- Page 12, display 3.10. A positive polynomial power is a polynomial of its truncated convolution. -/
theorem dirPoly_pow (a : ℕ → ℂ) {c1 c2 F : ℝ}
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 0 < F)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (g : ℕ) (hg : 0 < g) :
    Thm4.dirPoly a c1 c2 F χ s ^ g =
      Thm4.dirPoly (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) χ s := by
  rw [dirPoly_pow_eq_lift]
  apply lift_eq_dirPoly
  have hp : ∀ n ∈ (truncatedCoeffs a c1 c2 F).coeff.support,
      c1 * F < n ∧ (n : ℝ) < c2 * F := by
    intro n hn
    have hn' := Finsupp.mem_support_iff.mp hn
    rw [truncatedCoeffs_coeff] at hn'
    split_ifs at hn' with h
    · exact h
    · exact False.elim (hn' rfl)
  intro n hn
  simpa only [mul_pow] using coeff_pow_strict_bounds (truncatedCoeffs a c1 c2 F)
    (mul_pos hc1 hF) (mul_pos (hc1.trans hc2) hF) hp g hg n hn

/-- Page 12, the finite convolution formula at a positive index. -/
theorem coeff_mul_divisors (p r : MonoidAlgebra ℂ ℕ) {n : ℕ} (hn : n ≠ 0) :
    (p * r).coeff n = ∑ d ∈ n.divisors, p.coeff d * r.coeff (n / d) := by
  rw [MonoidAlgebra.coeff_mul_antidiag p r n n.divisorsAntidiagonal
    (by intro z; simp [Nat.mem_divisorsAntidiagonal, hn])]
  exact Nat.sum_divisorsAntidiagonal (fun d e => p.coeff d * r.coeff e)

/-- Pages 11 and 12, finite convolution of sequences vanishing at zero also vanishes there. -/
theorem coeff_mul_zero (p r : MonoidAlgebra ℂ ℕ)
    (hp : p.coeff 0 = 0) (hr : r.coeff 0 = 0) : (p * r).coeff 0 = 0 := by
  classical
  by_contra h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_mul.mp
    (MonoidAlgebra.support_coeff_mul_subset _ _ (Finsupp.mem_support_iff.mpr h))
  rcases mul_eq_zero.mp huv with h | h
  · subst u; exact (Finsupp.mem_support_iff.mp hu) hp
  · subst v; exact (Finsupp.mem_support_iff.mp hv) hr

/-- Page 12, divisor counts increase along divisibility at a positive index. -/
theorem divisor_count_mono {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    (d.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd)

/-- Page 12, a divisor-bounded sequence can be bounded by the ambient index. -/
theorem coeff_bound_at_divisor {a : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (ha : Thm4.CoeffBound a B) {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    ‖a d‖ ≤ (n.divisors.card : ℝ) ^ B := by
  exact (ha d).trans (Real.rpow_le_rpow (by positivity) (divisor_count_mono hn hd) hB)

/-- Page 12, convolution increases the divisor exponent by at most the sum plus one. -/
theorem coeff_mul_bound (p r : MonoidAlgebra ℂ ℕ) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0)
    (hp : Thm4.CoeffBound p.coeff B) (hr : Thm4.CoeffBound r.coeff D) :
    Thm4.CoeffBound (p * r).coeff (B + D + 1) := by
  intro n
  by_cases hn : n = 0
  · subst n
    rw [coeff_mul_zero p r hp0 hr0, norm_zero]
    positivity
  have ht : 0 < (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  rw [coeff_mul_divisors p r hn]
  calc
    ‖∑ d ∈ n.divisors, p.coeff d * r.coeff (n / d)‖ ≤
        ∑ d ∈ n.divisors, ‖p.coeff d * r.coeff (n / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (n.divisors.card : ℝ) ^ B * (n.divisors.card : ℝ) ^ D := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      exact mul_le_mul (coeff_bound_at_divisor hB hp hn (Nat.mem_divisors.mp hd).1)
        (coeff_bound_at_divisor hD hr hn (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1))
        (norm_nonneg _) (by positivity)
    _ = (n.divisors.card : ℝ) ^ (B + D + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Real.rpow_add ht, Real.rpow_add ht, Real.rpow_one]
      ring

/-- Page 12, every convolution power of a zero-at-zero sequence still vanishes at zero. -/
theorem coeff_pow_zero (p : MonoidAlgebra ℂ ℕ) (hp : p.coeff 0 = 0) (g : ℕ) :
    (p ^ g).coeff 0 = 0 := by
  induction g with
  | zero => simp [MonoidAlgebra.one_def]
  | succ g ih => rw [pow_succ]; exact coeff_mul_zero _ _ ih hp

/-- Page 12, the convolution identity coefficient sequence has divisor exponent zero. -/
theorem coeff_one_bound : Thm4.CoeffBound (1 : MonoidAlgebra ℂ ℕ).coeff 0 := by
  intro n
  by_cases hn : n = 1 <;> simp [MonoidAlgebra.one_def, hn]

/-- Page 12, repeated convolution preserves a divisor bound with a larger exponent. -/
theorem coeff_pow_bound (p : MonoidAlgebra ℂ ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hp0 : p.coeff 0 = 0) (hp : Thm4.CoeffBound p.coeff B) (g : ℕ) :
    Thm4.CoeffBound (p ^ g).coeff ((g : ℝ) * (B + 1)) := by
  induction g with
  | zero => simpa using coeff_one_bound
  | succ g ih =>
    have hh := coeff_mul_bound (p ^ g) p (by positivity) hB (coeff_pow_zero p hp0 g) hp0 ih hp
    rw [pow_succ]
    convert hh using 1 <;> push_cast <;> ring

/-- Pages 11 and 12, increasing a divisor exponent preserves a zero-at-zero coefficient bound. -/
theorem coeffBound_mono {a : ℕ → ℂ} {B D : ℝ} (ha0 : a 0 = 0)
    (ha : Thm4.CoeffBound a B) (hBD : B ≤ D) : Thm4.CoeffBound a D := by
  intro n
  by_cases hn : n = 0
  · subst n; rw [ha0, norm_zero]; positivity
  have ht : 1 ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  exact (ha n).trans (Real.rpow_le_rpow_of_exponent_le ht hBD)

/-- Page 12, truncation preserves the original divisor bound. -/
theorem truncatedCoeffs_bound {a : ℕ → ℂ} {B : ℝ} (ha : Thm4.CoeffBound a B)
    (c1 c2 F : ℝ) : Thm4.CoeffBound (truncatedCoeffs a c1 c2 F).coeff B := by
  intro n
  rw [truncatedCoeffs_coeff]
  split_ifs
  · exact ha n
  · rw [norm_zero]; positivity

/-- Page 12, a positive lower support endpoint excludes coefficient zero. -/
theorem truncatedCoeffs_zero (a : ℕ → ℂ) {c1 c2 F : ℝ} (h : 0 ≤ c1 * F) :
    (truncatedCoeffs a c1 c2 F).coeff 0 = 0 := by
  rw [truncatedCoeffs_coeff]
  simp [not_lt_of_ge h]

/-- Pages 11 and 12, a uniform coefficient bound controls the normalized coefficient energy. -/
theorem energy_le_uniform (a : ℕ → ℂ) {c1 c2 F M : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hF : 1 ≤ F) (hM : 0 ≤ M)
    (ha : ∀ n : ℕ, c1 * F < n → (n : ℝ) < c2 * F → ‖a n‖ ≤ M) :
    energy a c1 c2 F ≤ (c2 + 1) / c1 * M ^ 2 := by
  classical
  let S := (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  have hF0 : 0 < F := by linarith
  have hcard : (S.card : ℝ) ≤ (c2 + 1) * F := by
    have hh : S.card ≤ ⌊c2 * F⌋₊ + 1 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
    have hf := Nat.floor_le (show 0 ≤ c2 * F by positivity)
    have hh' : (S.card : ℝ) ≤ (⌊c2 * F⌋₊ : ℝ) + 1 := by exact_mod_cast hh
    nlinarith
  calc
    energy a c1 c2 F ≤ ∑ _n ∈ S, M ^ 2 / (c1 * F) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn1, hn2⟩ := (Finset.mem_filter.mp hn).2
      have hn0 : 0 < (n : ℝ) := (mul_pos hc1 hF0).trans hn1
      exact (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (ha n hn1 hn2) 2) hn0.le).trans
        (div_le_div_of_nonneg_left (sq_nonneg M) (mul_pos hc1 hF0) hn1.le)
    _ = (S.card : ℝ) * (M ^ 2 / (c1 * F)) := by simp
    _ ≤ ((c2 + 1) * F) * (M ^ 2 / (c1 * F)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (c2 + 1) / c1 * M ^ 2 := by field_simp

/-- Pages 11 and 12, a positive-power divisor bound gives positive-power coefficient growth. -/
theorem coeff_small_power
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    : ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ δ := by
  have hB1 : 0 < B + 1 := by linarith
  obtain ⟨C, hC, hbound⟩ := Akeno2026.Decomp86.card_divisors_le_rpow (ε := δ / (B + 1)) (div_pos hδ hB1)
  refine ⟨C ^ B, Real.rpow_pos_of_pos hC _, ?_⟩
  intro a ha n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have he : δ / (B + 1) * B ≤ δ := by
    have hh := div_mul_cancel₀ δ (ne_of_gt hB1)
    nlinarith [div_pos hδ hB1]
  calc
    ‖a n‖ ≤ (n.divisors.card : ℝ) ^ B := ha n
    _ ≤ (C * (n : ℝ) ^ (δ / (B + 1))) ^ B :=
      Real.rpow_le_rpow (by positivity) (hbound n) hB
    _ = C ^ B * (n : ℝ) ^ (δ / (B + 1) * B) := by
      rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul (by positivity)]
    _ ≤ C ^ B * (n : ℝ) ^ δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 he) (by positivity)

/-- Page 12, the coefficient energy is bounded by every positive power of the length. -/
theorem energy_small_power
    {B δ c1 c2 : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      ∀ F : ℝ, 1 ≤ F → energy a c1 c2 F ≤ C * F ^ δ := by
  obtain ⟨K, hK, hbound⟩ := coeff_small_power hB
    (show 0 < δ / 2 by linarith)
  refine ⟨(c2 + 1) / c1 * K ^ 2 * c2 ^ δ, by positivity, ?_⟩
  intro a ha F hF
  have hF0 : 0 < F := by linarith
  calc
    energy a c1 c2 F ≤ (c2 + 1) / c1 * (K * (c2 * F) ^ (δ / 2)) ^ 2 := by
      apply energy_le_uniform a hc1 hc2 hF (by positivity)
      intro n hn1 hn2
      have hn0 : 0 < (n : ℝ) := (mul_pos hc1 hF0).trans hn1
      have hn : 1 ≤ n := by exact_mod_cast (show 0 < (n : ℝ) from hn0)
      exact (hbound a ha n hn).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hn2.le (by linarith)) hK.le)
    _ = ((c2 + 1) / c1 * K ^ 2 * c2 ^ δ) * F ^ δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      norm_num
      rw [Real.mul_rpow hc2.le hF0.le]
      ring

/-- Page 12, apply moment estimates at a larger ambient x when taking a polynomial power. -/
theorem power_ambient_range {x F T : ℝ} {q g : ℕ}
    (hx : 2 ≤ x) (hF : 2 ≤ F) (hFx : F ≤ x) (hT : T ≤ x / 4)
    (hq : (q : ℝ) ≤ x) (hg : 1 ≤ g) :
    2 ≤ x ^ g ∧ 2 ≤ F ^ g ∧ F ^ g ≤ x ^ g ∧
      T ≤ x ^ g / 4 ∧ (q : ℝ) ≤ x ^ g ∧ Real.log (x ^ g) = (g : ℝ) * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hF1 : 1 ≤ F := by linarith
  have hxpow : x ≤ x ^ g := le_self_pow₀ hx1 (by omega)
  have hFpow : F ≤ F ^ g := le_self_pow₀ hF1 (by omega)
  exact ⟨hx.trans hxpow, hF.trans hFpow, pow_le_pow_left₀ (by linarith) hFx g,
    hT.trans (div_le_div_of_nonneg_right hxpow (by norm_num)), hq.trans hxpow,
    Real.log_pow x g⟩

/-- Page 12, display 3.10. Truncated convolution powers obey a uniform enlarged divisor exponent. -/
theorem truncated_power_bound {a : ℕ → ℂ} {B c1 c2 F : ℝ}
    (ha : Thm4.CoeffBound a B) (hc1 : 0 ≤ c1) (hF : 0 ≤ F) (g : ℕ) :
    Thm4.CoeffBound (truncatedCoeffs a c1 c2 F ^ g).coeff
      ((g : ℝ) * (max B 0 + 1)) := by
  have hz := truncatedCoeffs_zero a (c2 := c2) (mul_nonneg hc1 hF)
  exact coeff_pow_bound _ (le_max_right B 0) hz
    (coeffBound_mono hz (truncatedCoeffs_bound ha c1 c2 F) (le_max_left B 0)) g

/-- Page 12, display 3.10. Each fixed convolution power has energy bounded by every positive power of the original length. -/
theorem truncated_power_energy (B c1 c2 δ : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hδ : 0 < δ) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B → ∀ F : ℝ, 1 ≤ F →
      energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) ≤ C * F ^ δ := by
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  obtain ⟨C, hC, he⟩ := energy_small_power
    (B := (g : ℝ) * (max B 0 + 1)) (by positivity) (div_pos hδ hgR)
    (pow_pos hc1 g) (pow_pos hc2 g)
  refine ⟨C, hC, ?_⟩
  intro a ha F hF
  have hh := he (truncatedCoeffs a c1 c2 F ^ g).coeff
    (truncated_power_bound ha hc1.le (by linarith) g) (F ^ g) (one_le_pow₀ hF)
  rw [← Real.rpow_natCast_mul (by linarith : 0 ≤ F)] at hh
  have hexp : (g : ℝ) * (δ / (g : ℝ)) = δ := by field_simp
  rwa [hexp] at hh

/-- Page 12, display 3.10. The mean square input applies to every fixed polynomial power at a larger ambient x. -/
theorem power_mean_square (hmean : Lemma1MeanSquare) (B c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ (2 * g)) ≤
        C * Real.log x * ((q : ℝ) * T + F ^ g) *
          energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) := by
  have hg0 : g ≠ 0 := by omega
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  obtain ⟨C, hC, hm⟩ := hmean ((g : ℝ) * (max B 0 + 1)) (c1 ^ g) (c2 ^ g)
    (pow_pos hc1 _) (pow_lt_pow_left₀ hc2 hc1.le hg0)
  refine ⟨C * g, mul_pos hC hgR, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
  obtain ⟨hxg, hFg, hFxg, hTxg, hqxg, hlog⟩ := power_ambient_range hx hF hFx hTx hqx hg
  have hh := hm (x ^ g) (F ^ g) T q S (truncatedCoeffs a c1 c2 F ^ g).coeff
    (truncated_power_bound ha hc1.le (by linarith) g) hxg hFg hFxg hT hTxg hq hqxg hspace htimes
  calc
    _ = ∑ p ∈ S, ‖Thm4.dirPoly (truncatedCoeffs a c1 c2 F ^ g).coeff
        (c1 ^ g) (c2 ^ g) (F ^ g) p.2 (Thm4.half p.1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← dirPoly_pow a hc1 hc2 (by linarith) p.2 (Thm4.half p.1) g (by omega), norm_pow,
        ← pow_mul, Nat.mul_comm g 2]
    _ ≤ _ := hh
    _ = _ := by rw [hlog]; ring

/-- Page 12, display 3.10. The large value input applies to each fixed power with ambient x enlarged. -/
theorem power_large_values (hlarge : Lemma1LargeValues) (B c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      (S.card : ℝ) ≤ C * Real.log x ^ 2 *
        (energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) * F ^ g / V ^ (2 * g) +
          energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) ^ 3 *
            F ^ g * (q : ℝ) * T / V ^ (6 * g)) := by
  have hg0 : g ≠ 0 := by omega
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  obtain ⟨C, hC, hl⟩ := hlarge ((g : ℝ) * (max B 0 + 1)) (c1 ^ g) (c2 ^ g)
    (pow_pos hc1 _) (pow_lt_pow_left₀ hc2 hc1.le hg0)
  refine ⟨C * (g : ℝ) ^ 2, mul_pos hC (sq_pos_of_pos hgR), ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  obtain ⟨hxg, hFg, hFxg, hTxg, hqxg, hlog⟩ := power_ambient_range hx hF hFx hTx hqx hg
  have hh := hl (x ^ g) (F ^ g) T (V ^ g) q S (truncatedCoeffs a c1 c2 F ^ g).coeff
    (truncated_power_bound ha hc1.le (by linarith) g) hxg hFg hFxg hT hTxg hq hqxg
    (pow_pos hV _) hspace htimes (by
      intro p hp
      rw [← dirPoly_pow a hc1 hc2 (by linarith) p.2 (Thm4.half p.1) g (by omega), norm_pow]
      exact pow_le_pow_left₀ hV.le (hpoint p hp) g)
  calc
    (S.card : ℝ) ≤ _ := hh
    _ = _ := by
      simp only [hlog, mul_pow, ← pow_mul, Nat.mul_comm g 2, Nat.mul_comm g 6]
      ring

/-- Page 12, the integer dyadic levels between two positive norm cutoffs. -/
noncomputable def dyadicLevels (v V : ℝ) : Finset ℤ := Finset.Icc (Int.log 2 v) (Int.log 2 V)
/-- Page 12, a cell of the three polynomial norm levels. -/
noncomputable def dyadicCell {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    (k : ℤ × ℤ × ℤ) : Finset α := by
  classical
  exact S.filter (fun p => (Int.log 2 ‖f1 p‖, Int.log 2 ‖f2 p‖, Int.log 2 ‖f3 p‖) = k)
/-- Page 12, every value in a dyadic cell lies between its lower level and twice that level. -/
theorem dyadic_cell_bounds {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    (k : ℤ × ℤ × ℤ) {p : α} (hp : p ∈ dyadicCell S f1 f2 f3 k)
    (h1 : 0 < ‖f1 p‖) (h2 : 0 < ‖f2 p‖) (h3 : 0 < ‖f3 p‖) :
    (2 : ℝ) ^ k.1 ≤ ‖f1 p‖ ∧ ‖f1 p‖ < 2 * (2 : ℝ) ^ k.1 ∧
    (2 : ℝ) ^ k.2.1 ≤ ‖f2 p‖ ∧ ‖f2 p‖ < 2 * (2 : ℝ) ^ k.2.1 ∧
    (2 : ℝ) ^ k.2.2 ≤ ‖f3 p‖ ∧ ‖f3 p‖ < 2 * (2 : ℝ) ^ k.2.2 := by
  have he := (Finset.mem_filter.mp hp).2
  have hb (v : ℝ) (hv : 0 < v) :
      (2 : ℝ) ^ Int.log 2 v ≤ v ∧ v < 2 * (2 : ℝ) ^ Int.log 2 v := by
    refine ⟨Int.zpow_log_le_self (by norm_num) hv, ?_⟩
    simpa only [Nat.cast_ofNat, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using
      (Int.lt_zpow_succ_log_self (R := ℝ) (by norm_num : 1 < 2) v)
  rw [← he]
  exact ⟨(hb _ h1).1, (hb _ h1).2, (hb _ h2).1, (hb _ h2).2, (hb _ h3).1, (hb _ h3).2⟩

/-- Page 12, the finite dyadic partition preserves the sum exactly. -/
theorem dyadic_partition {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    {v V : ℝ} (hv : 0 < v)
    (h1 : ∀ p ∈ S, v ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ V)
    (h2 : ∀ p ∈ S, v ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ V)
    (h3 : ∀ p ∈ S, v ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ V) (w : α → ℝ) :
    ∑ k ∈ dyadicLevels v V ×ˢ dyadicLevels v V ×ˢ dyadicLevels v V,
      ∑ p ∈ dyadicCell S f1 f2 f3 k, w p = ∑ p ∈ S, w p := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro p hp
  have hmem (f : α → ℂ) (h : v ≤ ‖f p‖ ∧ ‖f p‖ ≤ V) :
      Int.log 2 ‖f p‖ ∈ dyadicLevels v V := by
    exact Finset.mem_Icc.mpr ⟨Int.log_mono_right hv h.1,
      Int.log_mono_right (hv.trans_le h.1) h.2⟩
  exact Finset.mem_product.mpr ⟨hmem f1 (h1 p hp),
    Finset.mem_product.mpr ⟨hmem f2 (h2 p hp), hmem f3 (h3 p hp)⟩⟩

/-- Page 12, summing a uniform cell bound costs at most the cube of the number of levels. -/
theorem dyadic_sum_bound {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    {v V H : ℝ} (hv : 0 < v)
    (h1 : ∀ p ∈ S, v ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ V)
    (h2 : ∀ p ∈ S, v ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ V)
    (h3 : ∀ p ∈ S, v ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ V)
    (hcell : ∀ k ∈ dyadicLevels v V ×ˢ dyadicLevels v V ×ˢ dyadicLevels v V,
      (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤ H) :
    (∑ p ∈ S, ‖f1 p * f2 p * f3 p‖) ≤ (dyadicLevels v V).card ^ 3 * H := by
  classical
  rw [← dyadic_partition S f1 f2 f3 hv h1 h2 h3 (fun p => ‖f1 p * f2 p * f3 p‖)]
  calc
    _ ≤ ∑ _k ∈ dyadicLevels v V ×ˢ dyadicLevels v V ×ˢ dyadicLevels v V, H :=
      Finset.sum_le_sum hcell
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul]; ring

/-- Page 12, the number of dyadic levels is the explicit integer interval cardinality. -/
theorem dyadic_level_count (v V : ℝ) :
    (dyadicLevels v V).card = (Int.log 2 V - Int.log 2 v + 1).toNat := by
  simpa [dyadicLevels, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    Int.card_Icc (Int.log 2 v) (Int.log 2 V)

/-- Page 12, the dyadic level count is at most the logarithmic range plus two. -/
theorem dyadic_level_count_le {v V : ℝ} (hv : 0 < v) (hV : v ≤ V) :
    ((dyadicLevels v V).card : ℝ) ≤ Real.logb 2 V - Real.logb 2 v + 2 := by
  have hm := Int.log_mono_right (b := 2) hv hV
  have hc : ((dyadicLevels v V).card : ℤ) = Int.log 2 V + 1 - Int.log 2 v :=
    Int.card_Icc_of_le (Int.log 2 v) (Int.log 2 V) (by omega)
  have hcR : ((dyadicLevels v V).card : ℝ) =
      (Int.log 2 V : ℝ) + 1 - (Int.log 2 v : ℝ) := by exact_mod_cast hc
  have hlow := Int.lt_floor_add_one (Real.logb 2 v)
  have hhigh := Int.floor_le (Real.logb 2 V)
  rw [show ⌊Real.logb 2 v⌋ = Int.log 2 v from
    Real.floor_logb_natCast (b := 2) hv.le] at hlow
  rw [show ⌊Real.logb 2 V⌋ = Int.log 2 V from
    Real.floor_logb_natCast (b := 2) (hv.le.trans hV)] at hhigh
  rw [hcR]
  linarith

/-- Page 12, points with one tiny polynomial have a direct product bound. -/
theorem tiny_product_bound {a b c : ℂ} {v U : ℝ} (hv : 0 ≤ v) (hU : 0 ≤ U)
    (ha : ‖a‖ ≤ U) (hb : ‖b‖ ≤ U) (hc : ‖c‖ ≤ U)
    (htiny : ‖a‖ ≤ v ∨ ‖b‖ ≤ v ∨ ‖c‖ ≤ v) :
    ‖a * b * c‖ ≤ v * U ^ 2 := by
  rw [norm_mul, norm_mul]
  rcases htiny with h | h | h
  · have hh := mul_le_mul (mul_le_mul h hb (norm_nonneg _) hv) hc
      (norm_nonneg _) (mul_nonneg hv hU)
    nlinarith
  · have hh := mul_le_mul (mul_le_mul ha h (norm_nonneg _) hU) hc
      (norm_nonneg _) (mul_nonneg hU hv)
    nlinarith
  · have hh := mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hU) h
      (norm_nonneg _) (mul_nonneg hU hU)
    nlinarith

/-- Page 12, a tiny-value contribution costs at most the cardinality times its pointwise bound. -/
theorem tiny_sum_bound {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    {v U : ℝ} (hv : 0 ≤ v) (hU : 0 ≤ U)
    (h1 : ∀ p ∈ S, ‖f1 p‖ ≤ U) (h2 : ∀ p ∈ S, ‖f2 p‖ ≤ U)
    (h3 : ∀ p ∈ S, ‖f3 p‖ ≤ U) :
    (∑ p ∈ S.filter (fun p => ‖f1 p‖ ≤ v ∨ ‖f2 p‖ ≤ v ∨ ‖f3 p‖ ≤ v),
      ‖f1 p * f2 p * f3 p‖) ≤ (S.card : ℝ) * v * U ^ 2 := by
  classical
  let R := S.filter (fun p => ‖f1 p‖ ≤ v ∨ ‖f2 p‖ ≤ v ∨ ‖f3 p‖ ≤ v)
  calc
    (∑ p ∈ R, ‖f1 p * f2 p * f3 p‖) ≤ ∑ _p ∈ R, v * U ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpS := (Finset.mem_filter.mp hp).1
      exact tiny_product_bound hv hU (h1 p hpS) (h2 p hpS) (h3 p hpS)
        (Finset.mem_filter.mp hp).2
    _ = (R.card : ℝ) * (v * U ^ 2) := by simp
    _ ≤ (S.card : ℝ) * (v * U ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = (S.card : ℝ) * v * U ^ 2 := by ring

/-- Page 14, one finite power cutoff works uniformly in the theta parameter. -/
theorem exists_uniform_power_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ g0 : ℕ, 1 ≤ g0 ∧ ∀ θ : ℝ, 0 ≤ θ → θ < 1 → θ - ε / 2 < Thm4.d θ g0 := by
  obtain ⟨g0, hg0⟩ := exists_nat_gt (1 / ε)
  have hgpos : 0 < (g0 : ℝ) := (one_div_pos.mpr hε).trans hg0
  refine ⟨g0, by exact_mod_cast (show (0 : ℝ) < g0 from hgpos), ?_⟩
  intro θ hθ0 hθ1
  have hh := Thm4.theta_sub_d θ g0 (Nat.cast_nonneg _)
  have hd : 0 < 2 * (g0 : ℝ) + 1 := by positivity
  have he : (1 - θ) / (2 * (g0 : ℝ) + 1) < ε / 2 := by
    rw [div_lt_iff₀ hd]
    have hg := (div_lt_iff₀ hε).mp hg0
    nlinarith
  linarith

/-- Pages 12 to 14, the admissible first exponent selects one of finitely many polynomial powers. -/
theorem exists_bounded_power {ε θ m n : ℝ} {g0 : ℕ} (hε : 0 < ε)
    (hθ : θ < 7 / 12) (h36 : |m - n| < 2 * θ - 1 - ε)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε) (hl : 0 ≤ 1 - m - n)
    (hg0 : θ - ε / 2 < Thm4.d θ g0) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ g0 ∧ Thm4.d θ ((g : ℝ) - 1) < m ∧ m ≤ Thm4.d θ g := by
  obtain ⟨hm0, hm1⟩ := Thm4.alpha1_range hε (by linarith) h36 h37 hl
  exact Thm4.exists_g g0 hm0 (hm1.trans hg0).le

/-- Pages 12 to 15, every fixed logarithmic loss is bounded by a small positive power. -/
theorem log_power_le_small_power {x A δ : ℝ} (hx : 1 ≤ x) (hA : 0 < A) (hδ : 0 < δ) :
    Real.log x ^ A ≤ (δ / A) ^ (-A) * x ^ δ := by
  have hx0 : 0 < x := by linarith
  have he : 0 < δ / A := div_pos hδ hA
  have hh := Real.rpow_le_rpow (Real.log_nonneg hx) (Real.log_le_rpow_div hx0.le he) hA.le
  calc
    Real.log x ^ A ≤ (x ^ (δ / A) / (δ / A)) ^ A := hh
    _ = (δ / A) ^ (-A) * x ^ δ := by
      rw [Real.div_rpow (by positivity) he.le, ← Real.rpow_mul hx0.le,
        div_mul_cancel₀ δ (ne_of_gt hA), Real.rpow_neg he.le A]
      ring

/-- Pages 12 to 15, a fixed power saving supplies every required logarithmic saving. -/
theorem power_saving_to_log_saving {x A δ β : ℝ}
    (hx : 1 < x) (hA : 0 < A) (hδ : 0 < δ) :
    x ^ (β - δ) ≤ (δ / A) ^ (-A) * x ^ β * Real.log x ^ (-A) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_neg hlog.le A, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hlog A)]
  calc
    x ^ (β - δ) * Real.log x ^ A ≤ x ^ (β - δ) * ((δ / A) ^ (-A) * x ^ δ) :=
      mul_le_mul_of_nonneg_left (log_power_le_small_power hx.le hA hδ) (by positivity)
    _ = (δ / A) ^ (-A) * x ^ β := by
      rw [mul_left_comm, ← Real.rpow_add hx0, sub_add_cancel]

/-- Page 13, Case 2 i has an epsilon over four power saving. -/
theorem case2i_margin {θ ε l : ℝ} (hl : l < Thm4.gam θ - ε) :
    (1 - θ) + l / 4 < 1 / 2 - ε / 4 := by
  have := Thm4.gam_le_one θ
  linarith

/-- Page 13, the first term of Case 2 ii has saving eleven epsilon over twenty-four. -/
theorem case2ii_I1_margin {θ ε l : ℝ} (hl : l < Thm4.gam θ - ε) :
    5 / 6 * (1 - θ) + (1 - l) / 24 + l / 2 < 1 / 2 - 11 * ε / 24 := by
  have := Thm4.gam_le_two θ
  linarith

/-- Page 13, the second term of Case 2 ii has saving eleven epsilon over seventy-two. -/
theorem case2ii_I2_margin {θ ε l : ℝ} (hl : l < Thm4.gam θ - ε) :
    (1 - θ) + (1 - l) / 72 + l / 6 < 1 / 2 - 11 * ε / 72 := by
  have := Thm4.gam_le_three θ
  linarith

/-- Page 14, Case 3 i has an epsilon over four power saving. -/
theorem case3i_margin {θ ε m n : ℝ} (h36 : |m - n| < 2 * θ - 1 - ε) :
    m / 2 + (1 - θ) / 2 + (1 - m - n) / 4 < 1 / 2 - ε / 4 := by
  have := Thm4.eq314 h36
  linarith

/-- Page 14, repaired Case 3 ii first term has a uniform epsilon over four saving for g at least two. -/
theorem case3ii_T1_margin {θ ε m n g : ℝ} (hg : 2 ≤ g) (hε : 0 < ε)
    (h36 : |m - n| < 2 * θ - 1 - ε) (hd : Thm4.d θ (g - 1) < m) :
    m / 2 + (1 - m - n) / 2 + (1 / 2 - 1 / (2 * g)) * (1 - θ) + n / (4 * g) <
      1 / 2 - ε / 4 := by
  have h1 := Thm4.eq314 h36
  have h2 := Thm4.corrected_sign hd
  have hg0 : 0 < g := by linarith
  have hd0 : 0 < 2 * g - 1 := by linarith
  have hn : (2 * g - 2) * (1 - θ) + (2 * g - 1) * ε < (2 * g - 1) * n := by
    have hh : 1 - m - n + m + ε < (1 + (2 * g - 2) * θ) / (2 * g - 1) := by linarith
    rw [lt_div_iff₀ hd0] at hh
    nlinarith
  have hid : m / 2 + (1 - m - n) / 2 + (1 / 2 - 1 / (2 * g)) * (1 - θ) + n / (4 * g) -
      (1 / 2 - ε / 4) =
      ((2 * g - 2) * (1 - θ) - (2 * g - 1) * n + g * ε) / (4 * g) := by
    field_simp
    ring
  rw [← sub_neg, hid]
  have hgap : 0 ≤ (g - 1) * ε := mul_nonneg (by linarith) hε.le
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

/-- Page 14, repaired Case 3 ii second term has a uniform epsilon over twelve saving. -/
theorem case3ii_T2_margin {θ ε m n g : ℝ} (hg : 1 ≤ g) (hε : 0 < ε)
    (h36 : |m - n| < 2 * θ - 1 - ε) (hd : m ≤ Thm4.d θ g) :
    m / 2 + (1 - m - n) / 6 + (1 - θ) / 2 + n / (12 * g) <
      1 / 2 - ε / 12 := by
  have h1 := Thm4.eq314 h36
  have h2 := Thm4.eq316_of_d hg hd
  have hg0 : 0 < g := by linarith
  have hd0 : 0 < 2 * g - 1 := by linarith
  have hl : (2 * g - 1) * (1 - m - n + ε) < 6 * g * θ - 1 - (6 * g - 1) * m := by
    have hh : 1 - m - n + ε < (6 * g * θ - 1 - (6 * g - 1) * m) / (2 * g - 1) := by linarith
    simpa only [mul_comm] using (lt_div_iff₀ hd0).mp hh
  have hid : m / 2 + (1 - m - n) / 6 + (1 - θ) / 2 + n / (12 * g) -
      (1 / 2 - ε / 12) =
      ((2 * g - 1) * (1 - m - n) - (6 * g * θ - 1 - (6 * g - 1) * m) + g * ε) / (12 * g) := by
    field_simp
    ring
  rw [← sub_neg, hid]
  have hgap : 0 ≤ (g - 1) * ε := mul_nonneg (by linarith) hε.le
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

/-- Page 14, the repaired g equal to one branch has an absolute one over 144 power saving. -/
theorem g1_uniform_margin {θ ε m n σ : ℝ} (hε : 0 < ε) (hθ : θ < 7 / 12)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε) (hd : m ≤ Thm4.d θ 1)
    (hc : n * Thm4.c σ < 1 - θ) :
    m / 2 + (1 - m - n) / 2 + n * (σ - 1 / 2) < 1 / 2 - 1 / 144 := by
  have hh := (Thm4.g1_repair hε hθ h37 hd hc).2
  have hg := Thm4.gam_le_one θ
  have hd1 : Thm4.d θ 1 = (4 * θ - 1) / 3 := by unfold Thm4.d; ring
  rw [hd1] at hd
  have hmin : 1 / 144 < min (n / 4) (n / 2 - (1 - θ) / 4) := by
    apply lt_min <;> linarith
  linarith

/-- Pages 11 and 12, positive-index small-power growth holds for every real divisor exponent. -/
theorem coeff_small_power_any (B δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ δ := by
  obtain ⟨C, hC, hc⟩ := coeff_small_power (le_max_right B 0) hδ
  refine ⟨C, hC, ?_⟩
  intro a ha n hn
  let b : ℕ → ℂ := fun k => if k = 0 then 0 else a k
  have hb0 : b 0 = 0 := by simp [b]
  have hb : Thm4.CoeffBound b B := by
    intro k
    by_cases hk : k = 0
    · subst k; rw [hb0, norm_zero]; positivity
    · simpa [b, hk] using ha k
  have hh := hc b (coeffBound_mono hb0 hb (le_max_left B 0)) n hn
  simpa [b, show n ≠ 0 by omega] using hh

/-- Page 12, a uniform polynomial upper bound controls the finite dyadic range. -/
theorem dirPoly_norm_uniform (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B → ∀ F : ℝ, 1 ≤ F →
      ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ≤ C * F ^ 2 := by
  classical
  obtain ⟨K, hK, hk⟩ := coeff_small_power_any B 1 (by norm_num)
  refine ⟨(c2 + 1) * K * c2, by positivity, ?_⟩
  intro a ha F hF q χ t
  have hF0 : 0 < F := by linarith
  let S := (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  have hcard : (S.card : ℝ) ≤ (c2 + 1) * F := by
    have hh : S.card ≤ ⌊c2 * F⌋₊ + 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
    have hf := Nat.floor_le (show 0 ≤ c2 * F by positivity)
    have hh' : (S.card : ℝ) ≤ (⌊c2 * F⌋₊ : ℝ) + 1 := by exact_mod_cast hh
    nlinarith
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ≤ K * c2 * F := by
    obtain ⟨hn1, hn2⟩ := (Finset.mem_filter.mp hn).2
    have hnpos : 0 < n := by exact_mod_cast ((mul_pos hc1 hF0).trans hn1)
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
    have hden : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hnR (by norm_num)
    rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [hre]
    calc
      ‖a n‖ * ‖χ (n : ZMod q)‖ / (n : ℝ) ^ (1 / 2 : ℝ) ≤ ‖a n‖ * ‖χ (n : ZMod q)‖ :=
        div_le_self (by positivity) hden
      _ ≤ ‖a n‖ := mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      _ ≤ K * n := by simpa using hk a ha n (by omega)
      _ ≤ K * c2 * F := by nlinarith
  calc
    ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ≤ ∑ n ∈ S,
        ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, K * c2 * F := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (K * c2 * F) := by simp
    _ ≤ ((c2 + 1) * F) * (K * c2 * F) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((c2 + 1) * K * c2) * F ^ 2 := by ring

/-- Page 12, display 3.10. Chebyshev for the powered polynomial gives its level cardinality estimate. -/
theorem power_square_cardinal (hmean : Lemma1MeanSquare) (B c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      (S.card : ℝ) ≤ C * Real.log x * ((q : ℝ) * T + F ^ g) *
        energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) / V ^ (2 * g) := by
  obtain ⟨C, hC, hm⟩ := power_mean_square hmean B c1 c2 hc1 hc2 g hg
  refine ⟨C, hC, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hh := cardinal_of_square_sum S
    (fun p => Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1) ^ g) (pow_pos hV _)
    (by
      intro p hp
      rw [norm_pow]
      exact pow_le_pow_left₀ hV.le (hpoint p hp) g)
    (by
      simpa only [norm_pow, ← pow_mul, Nat.mul_comm g 2] using
        hm x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes)
  simpa only [← pow_mul, Nat.mul_comm g 2] using hh

/-- Page 12, combining the second and sixth moment alternatives gives the minimum in 3.10. -/
theorem level_min_of_bounds {R H P Q V : ℝ} (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hmean : R ≤ H * (P / V ^ 2 + Q / V ^ 2))
    (hlarge : R ≤ H * (P / V ^ 2 + P * Q / V ^ 6)) :
    R ≤ H * (P / V ^ 2 + Q * min (1 / V ^ 2) (P / V ^ 6)) := by
  have hh := le_min hmean hlarge
  have hid : min (H * (P / V ^ 2 + Q / V ^ 2))
      (H * (P / V ^ 2 + P * Q / V ^ 6)) =
      H * (P / V ^ 2 + Q * min (1 / V ^ 2) (P / V ^ 6)) := by
    rw [mul_min_of_nonneg _ _ hQ, mul_add, mul_add, min_add_add_left,
      ← mul_min_of_nonneg _ _ hH]
    ring
  rwa [hid] at hh

/-- Pages 13 and 14, weighted interpolation of three nonnegative cardinal bounds. -/
theorem interpolate_three_bounds {R A B C u v w : ℝ}
    (hR : 0 ≤ R) (hA : R ≤ A) (hB : R ≤ B) (hC : R ≤ C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hsum : u + v + w = 1) :
    R ≤ A ^ u * B ^ v * C ^ w := by
  have hA0 : 0 ≤ A := hR.trans hA
  have hB0 : 0 ≤ B := hR.trans hB
  have hC0 : 0 ≤ C := hR.trans hC
  rcases hR.eq_or_lt with hzero | hpos
  · rw [← hzero]
    positivity
  calc
    R = R ^ u * R ^ v * R ^ w := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, hsum, Real.rpow_one]
    _ ≤ A ^ u * B ^ v * C ^ w := by
      exact mul_le_mul (mul_le_mul
        (Real.rpow_le_rpow hR hA hu) (Real.rpow_le_rpow hR hB hv)
        (by positivity) (by positivity)) (Real.rpow_le_rpow hR hC hw)
        (by positivity) (by positivity)

/-- Page 12, a cell contributes at most eight times its cardinality times its three lower levels. -/
theorem dyadic_cell_sum_le {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    (k : ℤ × ℤ × ℤ)
    (hpos : ∀ p ∈ S, 0 < ‖f1 p‖ ∧ 0 < ‖f2 p‖ ∧ 0 < ‖f3 p‖) :
    (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤
      (dyadicCell S f1 f2 f3 k).card * (8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) := by
  classical
  calc
    _ ≤ ∑ _p ∈ dyadicCell S f1 f2 f3 k,
        8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hpos p (Finset.mem_filter.mp hp).1
      obtain ⟨-, h1', -, h2', -, h3'⟩ := dyadic_cell_bounds S f1 f2 f3 k hp h1 h2 h3
      rw [norm_mul, norm_mul]
      have hh := mul_le_mul (mul_le_mul h1'.le h2'.le (norm_nonneg _) (by positivity))
        h3'.le (norm_nonneg _) (by positivity)
      nlinarith
    _ = _ := by simp

/-- Page 12, the cardinality terms for a polynomial power have exactly the printed exponents. -/
theorem power_level_exponents {F σ : ℝ} (hF : 1 ≤ F) (g : ℕ) :
    F ^ g / (F ^ (σ - 1 / 2)) ^ (2 * g) = (F ^ g) ^ (2 - 2 * σ) ∧
    1 / (F ^ (σ - 1 / 2)) ^ (2 * g) = (F ^ g) ^ (1 - 2 * σ) ∧
    F ^ g / (F ^ (σ - 1 / 2)) ^ (6 * g) = (F ^ g) ^ (4 - 6 * σ) := by
  have hF0 : 0 < F := by linarith
  have he (k : ℕ) : (F ^ (σ - 1 / 2)) ^ (k * g) =
      F ^ ((σ - 1 / 2) * ((k : ℝ) * g)) := by
    rw [← Real.rpow_mul_natCast hF0.le]
    norm_cast
  constructor
  · rw [he 2, ← Real.rpow_natCast F g, ← Real.rpow_sub hF0, ← Real.rpow_mul hF0.le]
    congr 1
    ring
  constructor
  · rw [he 2, one_div, ← Real.rpow_neg hF0.le, ← Real.rpow_natCast_mul hF0.le]
    congr 1
    ring
  · rw [he 6, ← Real.rpow_natCast F g, ← Real.rpow_sub hF0, ← Real.rpow_mul hF0.le]
    congr 1
    ring

/-- Pages 12 and 13, the minimum of the second and sixth moment powers is f of sigma. -/
theorem min_level_exponents {F σ : ℝ} (hF : 1 ≤ F) (g : ℕ) :
    min (1 / (F ^ (σ - 1 / 2)) ^ (2 * g))
      (F ^ g / (F ^ (σ - 1 / 2)) ^ (6 * g)) = (F ^ g) ^ Thm4.f σ := by
  obtain ⟨-, h2, h6⟩ := power_level_exponents hF g
  rw [h2, h6]
  unfold Thm4.f
  rcases le_total (1 - 2 * σ) (4 - 6 * σ) with h | h
  · rw [min_eq_left h, min_eq_left]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hF) h
  · rw [min_eq_right h, min_eq_right]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hF) h

/-- Page 12, one common coefficient-energy factor combines both supplied moment estimates. -/
theorem level_bound_of_energy {R Cm Cl L E G F Q V : ℝ}
    (hCm : 0 ≤ Cm) (hCl : 0 ≤ Cl) (hL : 0 ≤ L) (hE : 0 ≤ E) (hEG : E ≤ G)
    (hF : 0 ≤ F) (hQ : 0 ≤ Q) (hV : 0 < V)
    (hmean : R ≤ Cm * L * (Q + F) * E / V ^ 2)
    (hlarge : R ≤ Cl * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6)) :
    R ≤ (Cm + Cl) * (L + L ^ 2) * (G + G ^ 3) *
      (F / V ^ 2 + Q * min (1 / V ^ 2) (F / V ^ 6)) := by
  have hG : 0 ≤ G := hE.trans hEG
  have hG3 : 0 ≤ G ^ 3 := by positivity
  have hfactor : 0 ≤ (Cm + Cl) * (L + L ^ 2) * (G + G ^ 3) := by positivity
  apply level_min_of_bounds hfactor hQ
  · calc
      R ≤ Cm * L * (Q + F) * E / V ^ 2 := hmean
      _ ≤ (Cm + Cl) * (L + L ^ 2) * (Q + F) * (G + G ^ 3) / V ^ 2 := by
        gcongr
        · linarith
        · nlinarith [sq_nonneg L]
        · linarith
      _ = _ := by ring
  · have hE3 : E ^ 3 ≤ G ^ 3 := pow_le_pow_left₀ hE hEG 3
    have hE1 : E ≤ G + G ^ 3 := by linarith
    have hE3' : E ^ 3 ≤ G + G ^ 3 := by linarith
    calc
      R ≤ Cl * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6) := hlarge
      _ ≤ (Cm + Cl) * (L + L ^ 2) *
          ((G + G ^ 3) * F / V ^ 2 + (G + G ^ 3) * F * Q / V ^ 6) := by
        gcongr
        · linarith
        · linarith
      _ = _ := by ring

/-- Page 12, display 3.10. Both supplied moments give the exact minimum-form level bound for every fixed power. -/
theorem power_level_min (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      let E := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g)
      (S.card : ℝ) ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
  obtain ⟨Cm, hCm, hm⟩ := power_square_cardinal hmean B c1 c2 hc1 hc2 g hg
  obtain ⟨Cl, hCl, hl⟩ := power_large_values hlarge B c1 c2 hc1 hc2 g hg
  refine ⟨Cm + Cl, add_pos hCm hCl, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hhM := hm x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hhL := hl x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hE : 0 ≤ energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hh := level_bound_of_energy (R := (S.card : ℝ)) (Cm := Cm) (Cl := Cl)
    (L := Real.log x) (E := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g))
    (G := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g))
    (F := F ^ g) (Q := (q : ℝ) * T) (V := V ^ g)
    hCm.le hCl.le (Real.log_nonneg (by linarith)) hE (le_refl _)
    (by positivity) (by positivity) (pow_pos hV _)
    (by simpa only [← pow_mul, Nat.mul_comm g 2] using hhM)
    (by simpa only [← pow_mul, Nat.mul_comm g 2, Nat.mul_comm g 6, mul_assoc] using hhL)
  simpa only [← pow_mul, Nat.mul_comm g 2, Nat.mul_comm g 6, mul_assoc] using hh

/-- Pages 12 and 13, both branches of Case 2 give a uniform saving for a dyadic cell exponent. -/
theorem case2_cell_exponent {θ ε m n l σ1 σ2 σ3 s : ℝ}
    (hε : 0 < ε) (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l)
    (hsum : m + n + l = 1) (h37 : l < Thm4.gam θ - ε)
    (hM : s ≤ 1 - θ + m * Thm4.f σ1) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : s ≤ max (3 * l * (2 - 2 * σ3)) (1 - θ + 3 * l * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + l * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  by_cases h3 : σ3 ≤ 3 / 4
  · have hb := Thm4.case2i_bound (k := 1 - θ) (σ₁ := σ1) (σ₂ := σ2) hm hn hl h3
    have hf := case2i_margin h37
    nlinarith
  rcases le_max_iff.mp hL with hLa | hLb
  · have hi := Thm4.interp hM hN hLa
      (w₁ := 5 / 12) (w₂ := 5 / 12) (w₃ := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hb := Thm4.case2ii_I1 (1 - θ) m n l σ1 σ2 σ3 hm hn
    have hf := case2ii_I1_margin h37
    nlinarith
  · have hi := Thm4.interp hM hN hLb
      (w₁ := 17 / 36) (w₂ := 17 / 36) (w₃ := 1 / 18)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hb := Thm4.case2ii_I2 (1 - θ) m n l σ1 σ2 σ3 hm hn
    have hf := case2ii_I2_margin h37
    nlinarith

/-- Page 14, Case 3 i gives a uniform saving for a dyadic cell exponent. -/
theorem case3i_cell_exponent {θ ε m n σ1 σ2 σ3 s : ℝ}
    (hε : 0 < ε) (hn : 0 ≤ n) (hl : 0 ≤ 1 - m - n)
    (h36 : |m - n| < 2 * θ - 1 - ε) (h3 : σ3 ≤ 3 / 4)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  have hb := Thm4.case3i_bound (k := 1 - θ) (m := m) (σ₁ := σ1) (σ₂ := σ2) hn hl h3
  have hf := case3i_margin h36
  nlinarith

/-- Page 14, both Case 3 ii branches at g at least two give a uniform cell saving. -/
theorem case3ii_cell_exponent {θ ε m n σ1 σ2 σ3 s g : ℝ}
    (hε : 0 < ε) (hg : 2 ≤ g) (hn : 0 ≤ n)
    (h36 : |m - n| < 2 * θ - 1 - ε)
    (hdlo : Thm4.d θ (g - 1) < m) (hdhi : m ≤ Thm4.d θ g)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : s ≤ max (g * (1 - m - n) * (2 - 2 * σ3))
      (1 - θ + g * (1 - m - n) * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  have hg0 : 0 < g := by linarith
  have h2 : 1 / (2 * g) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h6 : 1 / (6 * g) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rcases le_max_iff.mp hL with hLa | hLb
  · have hi := Thm4.interp hM hN hLa
      (w₁ := 1 / 2) (w₂ := 1 / 2 - 1 / (2 * g)) (w₃ := 1 / (2 * g))
      (by norm_num) (by linarith) (by positivity) (by ring)
    have hb := Thm4.case3ii_T1 hg (1 - θ) m n (1 - m - n) σ1 σ2 σ3 hn
    have hf := case3ii_T1_margin hg hε h36 hdlo
    linarith
  · have hi := Thm4.interp hM hN hLb
      (w₁ := 1 / 2) (w₂ := 1 / 2 - 1 / (6 * g)) (w₃ := 1 / (6 * g))
      (by norm_num) (by linarith) (by positivity) (by ring)
    have hb := Thm4.case3ii_T2 (by linarith : 1 ≤ g) (1 - θ) m n (1 - m - n) σ1 σ2 σ3 hn
    have hf := case3ii_T2_margin (by linarith : 1 ≤ g) hε h36 hdhi
    linarith

/-- Page 14, the repaired g equal to one branch gives the same uniform cell saving. -/
theorem g1_cell_exponent {θ ε m n σ1 σ2 σ3 s : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1 / 2) (hθ : θ < 7 / 12) (hn : 0 ≤ n)
    (h36 : |m - n| < 2 * θ - 1 - ε)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε) (hd : m ≤ Thm4.d θ 1)
    (hc : n * Thm4.c σ2 < 1 - θ)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : s ≤ max ((1 - m - n) * (2 - 2 * σ3))
      (1 - θ + (1 - m - n) * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  rcases le_max_iff.mp hL with hLa | hLb
  · have hf := g1_uniform_margin hε hθ h37 hd hc
    nlinarith
  · have hi := Thm4.interp hM hN hLb
      (w₁ := 1 / 2) (w₂ := 1 / 3) (w₃ := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hb := Thm4.case3ii_T2 (g := 1) (by norm_num) (1 - θ) m n (1 - m - n) σ1 σ2 σ3 hn
    have hf := case3ii_T2_margin (g := 1) (by norm_num) hε h36 hd
    norm_num at hb hf
    linarith

/-- Page 13, Case 1 cancels the first two cell norm exponents exactly. -/
theorem case1_cell_exponent {m n σ1 σ2 s : ℝ}
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ n * (2 - 2 * σ2)) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) ≤ m / 2 + n / 2 := by
  have hh := Thm4.case1 m n σ1 σ2
  linarith

/-- Page 14, the mixed dominance case selects a bounded polynomial power and uses the repaired g equal to one branch. -/
theorem mixed_cell_exponent {θ ε m n σ1 σ2 σ3 s : ℝ} {g0 : ℕ}
    (hε : 0 < ε) (hεu : ε ≤ 1 / 2) (hθ : θ < 7 / 12)
    (hn : 0 ≤ n) (hl : 0 ≤ 1 - m - n)
    (h36 : |m - n| < 2 * θ - 1 - ε)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε)
    (hcut : θ - ε / 2 < Thm4.d θ g0)
    (hc : n * Thm4.c σ2 < 1 - θ)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : ∀ g : ℕ, 1 ≤ g → g ≤ g0 →
      s ≤ max ((g : ℝ) * (1 - m - n) * (2 - 2 * σ3))
        (1 - θ + (g : ℝ) * (1 - m - n) * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  by_cases h3 : σ3 ≤ 3 / 4
  · exact case3i_cell_exponent hε hn hl h36 h3 hM hN
  obtain ⟨g, hg1, hgg0, hdlo, hdhi⟩ := exists_bounded_power hε hθ h36 h37 hl hcut
  have hLg := hL g hg1 hgg0
  by_cases hg : g = 1
  · subst g
    simp only [Nat.cast_one, one_mul] at hLg hdhi
    exact g1_cell_exponent hε hεu hθ hn h36 h37 hdhi hc hM hN hLg
  · exact case3ii_cell_exponent hε (by exact_mod_cast (show 2 ≤ g by omega)) hn
      h36 hdlo hdhi hM hN hLg

/-- Pages 13 to 15, the four dominance cases reduce every cell to Case 1 or a uniform power saving. -/
theorem classify_cell_exponent {θ ε m n l σ1 σ2 σ3 s : ℝ} {g0 : ℕ}
    (hε : 0 < ε) (hεu : ε ≤ 1 / 2) (hθ : θ < 7 / 12)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l) (hsum : m + n + l = 1)
    (h36 : |m - n| < 2 * θ - 1 - ε) (h37 : l < Thm4.gam θ - ε)
    (hg0 : 3 ≤ g0) (hcut : θ - ε / 2 < Thm4.d θ g0)
    (hM : s ≤ max (m * (2 - 2 * σ1)) (1 - θ + m * Thm4.f σ1))
    (hN : s ≤ max (n * (2 - 2 * σ2)) (1 - θ + n * Thm4.f σ2))
    (hL : ∀ g : ℕ, 1 ≤ g → g ≤ g0 →
      s ≤ max ((g : ℝ) * l * (2 - 2 * σ3)) (1 - θ + (g : ℝ) * l * (4 - 6 * σ3))) :
    (s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) ≤ m / 2 + n / 2) ∨
    (s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + l * (σ3 - 1 / 2) < 1 / 2 - ε / 72) := by
  have hdom (a σ : ℝ) (hh : s ≤ max (a * (2 - 2 * σ)) (1 - θ + a * Thm4.f σ))
      (hd : 1 - θ ≤ a * Thm4.c σ) : s ≤ a * (2 - 2 * σ) := by
    rw [max_eq_left (Thm4.dominance.mpr hd)] at hh
    exact hh
  have hsmall (a σ : ℝ) (hh : s ≤ max (a * (2 - 2 * σ)) (1 - θ + a * Thm4.f σ))
      (hd : ¬ 1 - θ ≤ a * Thm4.c σ) : s ≤ 1 - θ + a * Thm4.f σ := by
    have hb : a * (2 - 2 * σ) ≤ 1 - θ + a * Thm4.f σ := by
      exact le_of_lt (lt_of_not_ge (fun h => hd (Thm4.dominance.mp h)))
    rwa [max_eq_right hb] at hh
  by_cases hdM : 1 - θ ≤ m * Thm4.c σ1
  · by_cases hdN : 1 - θ ≤ n * Thm4.c σ2
    · exact Or.inl (case1_cell_exponent (hdom m σ1 hM hdM) (hdom n σ2 hN hdN))
    · right
      have hlid : l = 1 - m - n := by linarith
      subst l
      exact mixed_cell_exponent hε hεu hθ hn hl h36 (by linarith) hcut
        (lt_of_not_ge hdN) (hdom m σ1 hM hdM) (hsmall n σ2 hN hdN) hL
  · by_cases hdN : 1 - θ ≤ n * Thm4.c σ2
    · right
      have hls : l = 1 - n - m := by linarith
      have hh := mixed_cell_exponent (m := n) (n := m) (σ1 := σ2) (σ2 := σ1)
        (σ3 := σ3) (s := s) hε hεu hθ hm (by linarith)
        (by simpa only [abs_sub_comm] using h36) (by linarith) hcut (lt_of_not_ge hdM)
        (hdom n σ2 hN hdN) (hsmall m σ1 hM hdM)
        (by intro g hg1 hgg0; simpa only [← hls] using hL g hg1 hgg0)
      rw [← hls] at hh
      linarith
    · right
      have hhL := hL 3 (by norm_num) hg0
      norm_num only [Nat.cast_ofNat] at hhL
      exact case2_cell_exponent hε hm hn hl hsum h37
        (hsmall m σ1 hM hdM) (hsmall n σ2 hN hdN) hhL

/-- Page 12, display 3.10 with an arbitrarily small power loss instead of a fixed logarithmic coefficient-energy loss. -/
theorem power_level_small_power (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (B c1 c2 δ : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) (hδ : 0 < δ) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      (S.card : ℝ) ≤ C * (1 + Real.log x) ^ 2 * F ^ δ *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
  obtain ⟨C0, hC0, hlevel⟩ := power_level_min hmean hlarge B c1 c2 hc1 hc2 g hg
  obtain ⟨D, hD, he⟩ := truncated_power_energy B c1 c2 (δ / 3) hc1 (hc1.trans hc2)
    (by linarith) g hg
  refine ⟨C0 * (D + D ^ 3), by positivity, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  let E := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g)
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hEF : E ≤ D * F ^ (δ / 3) := he a ha F (by linarith)
  have hF0 : 0 < F := by linarith
  have hEcube : E ^ 3 ≤ D ^ 3 * F ^ δ := by
    calc
      E ^ 3 ≤ (D * F ^ (δ / 3)) ^ 3 := pow_le_pow_left₀ hE hEF 3
      _ = D ^ 3 * F ^ δ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hF0.le]
        norm_num
  have hEsingle : E ≤ D * F ^ δ := hEF.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hD.le)
  have hEall : E + E ^ 3 ≤ (D + D ^ 3) * F ^ δ := by nlinarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogs : Real.log x + Real.log x ^ 2 ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have hh := hlevel x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  change (S.card : ℝ) ≤ C0 * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * _ at hh
  calc
    (S.card : ℝ) ≤ _ := hh
    _ ≤ C0 * (1 + Real.log x) ^ 2 * ((D + D ^ 3) * F ^ δ) *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
      gcongr
    _ = _ := by ring

/-- Pages 12 and 13, a positive-power energy loss cannot be absorbed by a fixed logarithmic allowance in Case 1. -/
theorem positive_power_not_log_bounded {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → x ^ δ ≤ C * Real.log x ^ A := by
  rintro ⟨C, hC⟩
  let c := 1 / (|C| + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop A hδ).def hc
  obtain ⟨x, hxsmall, hx⟩ := (hsmall.and (Filter.eventually_ge_atTop (2 : ℝ))).exists
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hxsmall
  have hpow : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 _
  have hratio : |C| * c < 1 := by
    dsimp [c]
    rw [one_div, ← div_eq_mul_inv, div_lt_one (by positivity)]
    linarith
  have hh : x ^ δ ≤ |C| * (c * x ^ δ) := calc
    x ^ δ ≤ C * Real.log x ^ A := hC x hx
    _ ≤ |C| * Real.log x ^ A := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (c * x ^ δ) := mul_le_mul_of_nonneg_left hxsmall (abs_nonneg C)
  nlinarith [mul_lt_mul_of_pos_right hratio hpow]

/-- Page 13, Case 1 has a uniform constant energy bound when the original divisor exponent is nonpositive. -/
theorem energy_nonpositive_exponent {a : ℕ → ℂ} {B c1 c2 F : ℝ}
    (hB : B ≤ 0) (ha : Thm4.CoeffBound a B) (hc1 : 0 < c1) (hc2 : 0 < c2) (hF : 1 ≤ F) :
    energy a c1 c2 F ≤ (c2 + 1) / c1 := by
  have hh := energy_le_uniform a hc1 hc2 hF (M := 1) (by norm_num) (by
    intro n hn1 hn2
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      have : 0 < c1 * F := mul_pos hc1 (by linarith)
      norm_num at hn1
      linarith
    have ht : 1 ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
    exact (ha n).trans (Real.rpow_le_one_of_one_le_of_nonpos ht hB))
  simpa using hh


open Classical Complex Thm4

set_option maxHeartbeats 40000000 in
/-- P0069 pages 12 to 15, the complete finite dyadic proof with its three explicit inputs.
The local facts reproduce the completed Decomp414a proof without a cyclic import.
Internal finite index types are specialized to Type zero, which contains the actual
real and character pair types. The sealed parent statement is unchanged.
CONDITIONAL ON the supplied hybrid mean square, hybrid large values and energy bounds. -/
theorem dyadic_mean_value (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) : Thm4.Theorem4Paper := by
  classical
  /- Page 13, the dominance test immediately above Case 1.
  For a nonzero value z, sigma is one half plus log norm z divided by log F.
  At zero the tag is harmless because the product summand is zero. -/
  let dominanceFlag (Q F : ℝ) (z : ℂ) : Bool :=
    decide (Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F))
  
  /- Pages 13 to 15, the part of a finite set with two prescribed dominance tags. -/
  let casePart {α : Type} (S : Finset α) (f g : α → Bool)
      (u v : Bool) : Finset α := S.filter (fun p => f p = u ∧ g p = v)
  
  /- Pages 13 to 15, finite sum partition into the four dominance cases.
  LeanSearch and Loogle find Finset.sum_filter_add_sum_filter_not.
  The Boolean normal form below is its twice-refined partition. -/
  have sum_four_parts {α : Type} (S : Finset α) (f g : α → Bool) (w : α → ℝ) :
      ∑ p ∈ S, w p =
        (∑ p ∈ casePart S f g true true, w p) +
        (∑ p ∈ casePart S f g false false, w p) +
        (∑ p ∈ casePart S f g true false, w p) +
        (∑ p ∈ casePart S f g false true, w p) := by
    simp only [casePart, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    cases hf : f p <;> cases hg : g p <;> simp [hf, hg]
  
  /- Page 15, Case 4 interchanges the two dominance coordinates. -/
  have casePart_swap {α : Type} (S : Finset α) (f g : α → Bool) (u v : Bool) :
      casePart S f g u v = casePart S g f v u := by
    ext p
    simp [casePart, and_comm]
  
  /- Page 13, local consistency of the two sides of the dominance test.
  The nonzero values 1 and 4 give opposite tags at Q equal to 8 and F equal to 4. -/
  have dominance_flag_instances :
      dominanceFlag 8 4 1 = false ∧ dominanceFlag 8 4 4 = true := by
    have hl : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    norm_num [dominanceFlag, Thm4.c, hl]
  
  
  /- Page 13, the dominance threshold written directly in terms of the norm.
  The power F to c of sigma is the maximum of F and the fourth power of the norm. -/
  have dominance_power_eq_max {F : ℝ} (hF : 1 < F) (z : ℂ) :
      F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F) = max F (‖z‖ ^ 4) := by
    have hF0 : 0 < F := by linarith
    have hlF : Real.log F ≠ 0 := ne_of_gt (Real.log_pos hF)
    by_cases hz : ‖z‖ = 0
    · norm_num [hz, Thm4.c, max_eq_left hF0.le]
    have hz0 : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    let σ : ℝ := 1 / 2 + Real.log ‖z‖ / Real.log F
    have he : F ^ (4 * σ - 2) = ‖z‖ ^ 4 := by
      rw [Real.rpow_def_of_pos hF0]
      have hh : Real.log F * (4 * σ - 2) = Real.log ‖z‖ * 4 := by
        dsimp [σ]
        field_simp [hlF]
        ring
      rw [hh, Real.exp_mul, Real.exp_log hz0]
      norm_num
    by_cases hσ : σ ≤ 3 / 4
    · have hv : ‖z‖ ^ 4 ≤ F := by
        rw [← he]
        exact (Real.rpow_le_rpow_of_exponent_le hF.le (by linarith : 4 * σ - 2 ≤ 1)).trans_eq
          (Real.rpow_one F)
      change F ^ Thm4.c σ = _
      rw [Thm4.c, if_pos hσ, Real.rpow_one, max_eq_left hv]
    · have hv : F ≤ ‖z‖ ^ 4 := by
        calc
          F = F ^ (1 : ℝ) := (Real.rpow_one F).symm
          _ ≤ F ^ (4 * σ - 2) := Real.rpow_le_rpow_of_exponent_le hF.le (by linarith)
          _ = _ := he
      change F ^ Thm4.c σ = _
      rw [Thm4.c, if_neg hσ, he, max_eq_right hv]
  
  /- Page 13, a dominant value above the character-time scale has fourth power at least qT. -/
  have dominant_value_fourth {Q F : ℝ} (hF : 1 < F) (hQ : F < Q) {z : ℂ}
      (hz : dominanceFlag Q F z = true) : Q ≤ ‖z‖ ^ 4 := by
    have hh : Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F) := of_decide_eq_true hz
    rw [dominance_power_eq_max hF] at hh
    exact (le_max_iff.mp hh).resolve_left (not_le.mpr hQ)
  
  /- Page 12, the one-polynomial version of the finite dyadic partition.
  Summing a uniform square-moment bound over the actual norm levels costs
  only the number of levels. -/
  have square_sum_of_dyadic_cells {ι : Type} (S : Finset ι) (f : ι → ℂ)
      {U H : ℝ} (hU : ∀ p ∈ S, 1 ≤ ‖f p‖ ∧ ‖f p‖ ≤ U)
      (hc : ∀ k ∈ dyadicLevels 1 U,
        (∑ p ∈ S.filter (fun p => Int.log 2 ‖f p‖ = k), ‖f p‖ ^ 2) ≤ H) :
      (∑ p ∈ S, ‖f p‖ ^ 2) ≤ (dyadicLevels 1 U).card * H := by
    have he : (∑ k ∈ dyadicLevels 1 U,
        ∑ p ∈ S.filter (fun p => Int.log 2 ‖f p‖ = k), ‖f p‖ ^ 2) =
        ∑ p ∈ S, ‖f p‖ ^ 2 := by
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      exact Finset.mem_Icc.mpr ⟨Int.log_mono_right (by norm_num : (0 : ℝ) < 1) (hU p hp).1,
        Int.log_mono_right (by linarith [(hU p hp).1]) (hU p hp).2⟩
    rw [← he]
    exact (Finset.sum_le_sum hc).trans_eq (by simp)
  
  /- Page 13, displays 3.11 and 3.12. Within a dyadic cell, the large-value
  estimate and Q at most sixteen V to the fourth give a uniform square sum.
  The energy and the cited cardinality estimate are explicit scalar inputs. -/
  have square_sum_of_cardinal_bound {ι : Type} (S : Finset ι) (f : ι → ℂ)
      {C L E F Q V : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hE : 0 ≤ E) (hF : 0 ≤ F)
      (hV : 0 < V) (hQ : Q ≤ 16 * V ^ 4)
      (hpoint : ∀ p ∈ S, ‖f p‖ ≤ 2 * V)
      (hcard : (S.card : ℝ) ≤ C * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6)) :
      (∑ p ∈ S, ‖f p‖ ^ 2) ≤ 4 * C * L ^ 2 * F * (E + 16 * E ^ 3) := by
    have hsum : (∑ p ∈ S, ‖f p‖ ^ 2) ≤ (S.card : ℝ) * (4 * V ^ 2) := by
      calc
        _ ≤ ∑ _p ∈ S, (2 * V) ^ 2 := Finset.sum_le_sum
          (fun p hp => pow_le_pow_left₀ (norm_nonneg _) (hpoint p hp) 2)
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    have hcard' := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 4 * V ^ 2)
    have heq : C * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6) * (4 * V ^ 2) =
        4 * C * L ^ 2 * F * (E + E ^ 3 * Q / V ^ 4) := by
      field_simp [hV.ne']
      <;> ring
    rw [heq] at hcard'
    apply hsum.trans (hcard'.trans _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hq : Q / V ^ 4 ≤ 16 := (div_le_iff₀ (by positivity)).mpr hQ
    have hh := mul_le_mul_of_nonneg_left hq (pow_nonneg hE 3)
    have he : E ^ 3 * Q / V ^ 4 = E ^ 3 * (Q / V ^ 4) := by ring
    rw [he]
    linarith
  
  /- Pages 12 and 13, displays 3.4 and 3.11 applied to one actual dominant cell.
  Only the large-value input is used. The coefficient energy remains explicit.
  CONDITIONAL on Lemma1LargeValues. -/
  have dominant_dyadic_square_bound (hlarge : Lemma1LargeValues)
      (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) :
      ∃ C : ℝ, 0 < C ∧ ∀ x F T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 →
      1 ≤ q → (q : ℝ) ≤ x → F < (q : ℝ) * T →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, dominanceFlag ((q : ℝ) * T) F (dirPoly a c1 c2 F p.2 (half p.1)) = true) →
      ∀ k : ℤ,
        (∑ p ∈ S.filter (fun p => Int.log 2 ‖dirPoly a c1 c2 F p.2 (half p.1)‖ = k),
          ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
        4 * C * Real.log x ^ 2 * F * (energy a c1 c2 F + 16 * energy a c1 c2 F ^ 3) := by
    obtain ⟨C, hC, hc⟩ := hlarge B c1 c2 hc1 hc2
    refine ⟨C, hC, ?_⟩
    intro x F T q S a ha hx hF hFx hT hTx hq hqx hQ hspace htimes hdom k
    let f : (ℝ × DirichletCharacter ℂ q) → ℂ := fun p => dirPoly a c1 c2 F p.2 (half p.1)
    let P := S.filter (fun p => Int.log 2 ‖f p‖ = k)
    let V : ℝ := (2 : ℝ) ^ k
    have hV : 0 < V := by dsimp [V]; positivity
    have hE : 0 ≤ energy a c1 c2 F := Finset.sum_nonneg (fun n hn => by positivity)
    have hsub : P ⊆ S := Finset.filter_subset _ _
    have hfourth (p) (hp : p ∈ P) : (q : ℝ) * T ≤ ‖f p‖ ^ 4 :=
      dominant_value_fourth (by linarith) hQ (hdom p (hsub hp))
    have hpos (p) (hp : p ∈ P) : 0 < ‖f p‖ := by
      by_contra! hh
      have hz : ‖f p‖ = 0 := le_antisymm hh (norm_nonneg _)
      have hfour := hfourth p hp
      rw [hz] at hfour
      norm_num at hfour
      linarith
    have hlevels (p) (hp : p ∈ P) : V ≤ ‖f p‖ ∧ ‖f p‖ < 2 * V := by
      have he := (Finset.mem_filter.mp hp).2
      have hlo := Int.zpow_log_le_self (by norm_num : 1 < (2 : ℕ)) (hpos p hp)
      have hhi := Int.lt_zpow_succ_log_self (R := ℝ) (by norm_num : 1 < 2) ‖f p‖
      rw [he] at hlo hhi
      exact ⟨hlo, by simpa only [V, Nat.cast_ofNat, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hhi⟩
    by_cases hempty : P = ∅
    · change (∑ p ∈ P, ‖f p‖ ^ 2) ≤ _
      rw [hempty, Finset.sum_empty]
      positivity
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hQcell : (q : ℝ) * T ≤ 16 * V ^ 4 := by
      calc
        _ ≤ ‖f p‖ ^ 4 := hfourth p hp
        _ ≤ (2 * V) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (hlevels p hp).2.le 4
        _ = _ := by ring
    have hsp : WellSpaced P := by
      intro p hp p' hp' hne heq
      exact hspace p (hsub hp) p' (hsub hp') hne heq
    have hcard := hc x F T V q P a ha hx hF hFx hT hTx hq hqx hV hsp
      (fun p hp => htimes p (hsub hp)) (fun p hp => (hlevels p hp).1)
    exact square_sum_of_cardinal_bound P f hC.le (Real.log_nonneg (by linarith)) hE
      (by linarith) hV hQcell (fun p hp => (hlevels p hp).2.le) (by simpa only [mul_assoc] using hcard)
  
  
  
  
  /- Page 12, the logarithmic energy bound can use log x uniformly for F at most x.
  The exponent is made nonnegative. No divisor moment estimate is asserted here.
  CONDITIONAL on the explicit EnergyLogBound input. -/
  have energy_log_uniform (henergy : EnergyLogBound)
      (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) :
      ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ a : ℕ → ℂ, CoeffBound a B →
      ∀ x F : ℝ, 1 ≤ Real.log x → 2 ≤ F → F ≤ x →
        energy a c1 c2 F ≤ C * Real.log x ^ K := by
    obtain ⟨K0, C0, hC0, he⟩ := henergy B c1 c2 hc1 hc2
    let C := C0 * (1 + Real.log 2 ^ K0)
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, |K0|, hC, abs_nonneg _, ?_⟩
    intro a ha x F hx hF hFx
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlF : Real.log 2 ≤ Real.log F := Real.log_le_log (by norm_num) hF
    have hlFx : Real.log F ≤ Real.log x := Real.log_le_log (by linarith) hFx
    have hlx : 0 < Real.log x := by linarith
    have hK : 1 ≤ Real.log x ^ |K0| := Real.one_le_rpow hx (abs_nonneg _)
    have hpow : Real.log F ^ K0 ≤ (1 + Real.log 2 ^ K0) * Real.log x ^ |K0| := by
      by_cases hK0 : 0 ≤ K0
      · have hh : Real.log F ^ K0 ≤ Real.log x ^ |K0| := by
          rw [abs_of_nonneg hK0]
          exact Real.rpow_le_rpow (by linarith) hlFx hK0
        have ht : 0 ≤ Real.log 2 ^ K0 := Real.rpow_nonneg hl2.le _
        nlinarith [Real.rpow_nonneg hlx.le |K0|]
      · have hh : Real.log F ^ K0 ≤ Real.log 2 ^ K0 :=
          Real.rpow_le_rpow_of_nonpos hl2 hlF (le_of_not_ge hK0)
        have ht : 0 ≤ Real.log 2 ^ K0 := Real.rpow_nonneg hl2.le _
        nlinarith
    exact (he a ha F hF).trans (by
      have hh := mul_le_mul_of_nonneg_left hpow hC0.le
      convert hh using 1 <;> dsimp [C] <;> ring)
  
  /- Page 12, a fixed quadratic upper bound for the norm gives only logarithmically many levels.
  This uses the existing exact finite dyadic count. -/
  have quadratic_level_count {C x : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x)
      (hlx : 1 ≤ Real.log x) :
      ((dyadicLevels 1 (C * x ^ 2)).card : ℝ) ≤
        ((Real.log C + 2) / Real.log 2 + 2) * Real.log x := by
    have hC0 : 0 < C := by linarith
    have hx0 : 0 < x := by linarith
    have hU : 1 ≤ C * x ^ 2 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hx)
    have h := dyadic_level_count_le (by norm_num : (0 : ℝ) < 1) hU
    have he : Real.log (C * x ^ 2) = Real.log C + 2 * Real.log x := by
      rw [Real.log_mul hC0.ne' (pow_pos hx0 2).ne', Real.log_pow]
      norm_num
    rw [Real.logb, Real.logb, Real.log_one, zero_div, sub_zero, he] at h
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
    have hh : (Real.log C + 2 * Real.log x) / Real.log 2 + 2 ≤
        ((Real.log C + 2) / Real.log 2 + 2) * Real.log x := by
      apply (le_of_sub_nonneg _)
      have heq : ((Real.log C + 2) / Real.log 2 + 2) * Real.log x -
          ((Real.log C + 2 * Real.log x) / Real.log 2 + 2) =
          (Real.log C / Real.log 2 + 2) * (Real.log x - 1) := by ring
      rw [heq]
      positivity
    exact h.trans hh
  
  /- Page 12, one nonnegative logarithmic energy exponent controls both energies in 3.4. -/
  have energy_cubic_log_bound {E C K L : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C)
      (hK : 0 ≤ K) (hL : 1 ≤ L) (he : E ≤ C * L ^ K) :
      E + 16 * E ^ 3 ≤ (C + 16 * C ^ 3) * L ^ (3 * K) := by
    have hL0 : 0 < L := by linarith
    have he1 : E ≤ C * L ^ (3 * K) := he.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hC)
    have he3 : E ^ 3 ≤ C ^ 3 * L ^ (3 * K) := by
      calc
        _ ≤ (C * L ^ K) ^ 3 := pow_le_pow_left₀ hE he 3
        _ = _ := by
          rw [mul_pow, ← Real.rpow_mul_natCast hL0.le]
          congr 2
          norm_num
          ring
    nlinarith
  
  
  
  
  /- Pages 12 and 13, displays 3.11 and 3.12, summed on the dominant values.
  The low character-time range uses the mean square estimate directly.
  The other range uses the actual dyadic cells and their logarithmic count.
  CONDITIONAL on the three explicit analytic premises. No cited sorry is called. -/
  have dominant_square_moment (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 →
      ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, CoeffBound a B →
      2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, dominanceFlag ((q : ℝ) * T) F (dirPoly a c1 c2 F p.2 (half p.1)) = true) →
      (∑ p ∈ S, ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
        C * F * Real.log x ^ D := by
    intro B c1 c2 hc1 hc2
    obtain ⟨Cm, hCm, hm⟩ := hmean B c1 c2 hc1 hc2
    obtain ⟨Cl, hCl, hcell⟩ := dominant_dyadic_square_bound hlarge B c1 c2 hc1 hc2
    obtain ⟨Ce, K, hCe, hK, he⟩ := energy_log_uniform henergy B c1 c2 hc1 hc2
    obtain ⟨Cn, hCn, hpoly⟩ := dirPoly_norm_uniform B c1 c2 hc1 (hc1.trans hc2)
    let J := (Real.log (Cn + 1) + 2) / Real.log 2 + 2
    have hJ : 0 < J := by
      have hh : 0 ≤ Real.log (Cn + 1) := Real.log_nonneg (by linarith)
      have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      dsimp [J]
      positivity
    let C := 2 * Cm * Ce + 4 * Cl * J * (Ce + 16 * Ce ^ 3)
    let D := 3 * K + 3
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, D, hC, by dsimp [D]; linarith, ?_⟩
    intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes hdom
    have hx3 : 3 ≤ x := by linarith
    have hlx : 1 ≤ Real.log x := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
      linarith [Real.log_three_gt_d9]
    have hlx0 : 0 < Real.log x := by linarith
    have hF0 : 0 ≤ F := by linarith
    have hE : 0 ≤ energy a c1 c2 F := Finset.sum_nonneg (fun n hn => by positivity)
    have henergyF := he a ha x F hlx hF hFx
    have hClo : 2 * Cm * Ce ≤ C := by
      dsimp [C]
      have hh : 0 ≤ 4 * Cl * J * (Ce + 16 * Ce ^ 3) := by positivity
      linarith
    have hChi : 4 * Cl * J * (Ce + 16 * Ce ^ 3) ≤ C := by
      dsimp [C]
      have hh : 0 ≤ 2 * Cm * Ce := by positivity
      linarith
    by_cases hQ : (q : ℝ) * T ≤ F
    · have hs := hm x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
      have hpow : Real.log x * Real.log x ^ K ≤ Real.log x ^ D := by
        have heq : Real.log x * Real.log x ^ K = Real.log x ^ (1 + K) := by
          rw [Real.rpow_add hlx0, Real.rpow_one]
        rw [heq]
        exact Real.rpow_le_rpow_of_exponent_le hlx (by dsimp [D]; linarith)
      calc
        _ ≤ Cm * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := hs
        _ ≤ Cm * Real.log x * (2 * F) * (Ce * Real.log x ^ K) := by gcongr <;> linarith
        _ = (2 * Cm * Ce) * F * (Real.log x * Real.log x ^ K) := by ring
        _ ≤ C * F * Real.log x ^ D := mul_le_mul
          (mul_le_mul_of_nonneg_right hClo hF0) hpow (by positivity) (by positivity)
    have hQ' : F < (q : ℝ) * T := lt_of_not_ge hQ
    let f : (ℝ × DirichletCharacter ℂ q) → ℂ := fun p => dirPoly a c1 c2 F p.2 (half p.1)
    let U : ℝ := (Cn + 1) * x ^ 2
    have hvalues : ∀ p ∈ S, 1 ≤ ‖f p‖ ∧ ‖f p‖ ≤ U := by
      intro p hp
      have hfour := dominant_value_fourth (by linarith : 1 < F) hQ' (hdom p hp)
      have hn1 : 1 ≤ ‖f p‖ := by
        by_contra! hn
        have hh := pow_lt_pow_left₀ hn (norm_nonneg (f p)) (by norm_num : (4 : ℕ) ≠ 0)
        norm_num at hh
        change (q : ℝ) * T ≤ ‖f p‖ ^ 4 at hfour
        linarith
      refine ⟨hn1, ?_⟩
      calc
        _ ≤ Cn * F ^ 2 := hpoly a ha F (by linarith) q p.2 p.1
        _ ≤ (Cn + 1) * x ^ 2 := mul_le_mul (by linarith) (pow_le_pow_left₀ hF0 hFx 2)
          (sq_nonneg _) (by linarith)
    have hcount : ((dyadicLevels 1 U).card : ℝ) ≤ J * Real.log x :=
      quadratic_level_count (by linarith) (by linarith) hlx
    have hEcube := energy_cubic_log_bound hE hCe.le hK hlx henergyF
    have hsum := square_sum_of_dyadic_cells S f hvalues
      (fun k hk => hcell x F T q S a ha hx hF hFx hT hTx hq hqx hQ' hspace htimes hdom k)
    have hlogeq : Real.log x ^ (3 * K) * Real.log x ^ 2 * Real.log x = Real.log x ^ D := by
      calc
        _ = Real.log x ^ (3 * K) * Real.log x ^ (2 : ℝ) * Real.log x ^ (1 : ℝ) := by simp
        _ = Real.log x ^ (3 * K + 2 + 1) := by rw [← Real.rpow_add hlx0, ← Real.rpow_add hlx0]
        _ = _ := by congr 1; dsimp [D]; ring
    calc
      _ ≤ (dyadicLevels 1 U).card *
          (4 * Cl * Real.log x ^ 2 * F * (energy a c1 c2 F + 16 * energy a c1 c2 F ^ 3)) := hsum
      _ ≤ (J * Real.log x) *
          (4 * Cl * Real.log x ^ 2 * F * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K))) :=
        mul_le_mul hcount (mul_le_mul_of_nonneg_left hEcube (by positivity)) (by positivity) (by positivity)
      _ = (4 * Cl * J * (Ce + 16 * Ce ^ 3)) * F *
          (Real.log x ^ (3 * K) * Real.log x ^ 2 * Real.log x) := by ring
      _ = (4 * Cl * J * (Ce + 16 * Ce ^ 3)) * F * Real.log x ^ D := by rw [hlogeq]
      _ ≤ C * F * Real.log x ^ D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hChi hF0) (by positivity)
  
  
  
  
  
  /- Page 13, Case 1. Cauchy Schwarz combines the two dominant square moments.
  The explicit hypotheses are finite moment bounds, not cited theorems. -/
  have pair_of_square_bounds {ι : Type} (S : Finset ι) (f g : ι → ℂ)
      {C M N L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 ≤ L)
      (hf : (∑ p ∈ S, ‖f p‖ ^ 2) ≤ C * M * L)
      (hg : (∑ p ∈ S, ‖g p‖ ^ 2) ≤ C * N * L) :
      (∑ p ∈ S, ‖f p * g p‖) ≤ C * Real.sqrt M * Real.sqrt N * L := by
    simp_rw [norm_mul]
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => ‖f p‖) (fun p => ‖g p‖)
    have hs := mul_le_mul hf hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (mul_nonneg (mul_nonneg hC hM) hL)
    have he : (C * Real.sqrt M * Real.sqrt N * L) ^ 2 = (C * M * L) * (C * N * L) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hN]
      ring
    have hp : 0 ≤ C * Real.sqrt M * Real.sqrt N * L := by positivity
    nlinarith
  
  /- Page 13, Case 1. Extract the uniform third-factor bound from the finite sum. -/
  have triple_of_pair_bound {ι : Type} (S : Finset ι) (f g e : ι → ℂ)
      {H U : ℝ} (hU : 0 ≤ U)
      (hpair : (∑ p ∈ S, ‖f p * g p‖) ≤ H)
      (he : ∀ p ∈ S, ‖e p‖ ≤ U) :
      (∑ p ∈ S, ‖f p * g p * e p‖) ≤ H * U := by
    calc
      _ ≤ ∑ p ∈ S, ‖f p * g p‖ * U := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (he p hp) (norm_nonneg _)
      _ = (∑ p ∈ S, ‖f p * g p‖) * U := (Finset.sum_mul ..).symm
      _ ≤ H * U := mul_le_mul_of_nonneg_right hpair hU
  
  
  
  
  
  
  /- Page 13, the Case 2 split at sigma3 equal to three quarters.
  The small part consists of third-factor norms at most length to one quarter. -/
  let thirdNormPart {ι : Type} (S : Finset ι) (f : ι → ℂ) (L : ℝ)
      (small : Bool) : Finset ι := S.filter (fun p => decide (‖f p‖ ≤ L ^ (1 / 4 : ℝ)) = small)
  
  /- Page 13, both third-factor branches partition the actual finite norm sum. -/
  have sum_third_parts {ι : Type} (S : Finset ι) (f : ι → ℂ) (L : ℝ) (w : ι → ℝ) :
      ∑ p ∈ S, w p = (∑ p ∈ thirdNormPart S f L true, w p) +
        ∑ p ∈ thirdNormPart S f L false, w p := by
    simpa [thirdNormPart] using
      (Finset.sum_filter_add_sum_filter_not S (fun p => ‖f p‖ ≤ L ^ (1 / 4 : ℝ)) w).symm
  
  /- Page 13, a value on the nondominant side forces the character-time scale above the length. -/
  have nondominant_scale_lt {Q F : ℝ} (hF : 1 < F) {z : ℂ}
      (hz : dominanceFlag Q F z = false) : F < Q := by
    have hh : ¬Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F) := of_decide_eq_false hz
    rw [dominance_power_eq_max hF] at hh
    exact lt_of_not_ge (fun h => hh (h.trans (le_max_left _ _)))
  
  /- Page 13, the Case 2 power saving absorbs a fixed positive logarithmic loss.
  The large base X is allowed to exceed x, as in the paper's two choices of X. -/
  have power_saving_with_log {x X A δ k : ℝ} (hx : 1 < x) (hX : x ≤ X)
      (hA : 0 < A) (hδ : 0 < δ) (hk : 0 ≤ k) :
      X ^ (1 / 2 - δ) * Real.log x ^ k ≤
        (δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    have hA' : 0 < A + k := by linarith
    have hlx : 0 < Real.log x := Real.log_pos hx
    have hlX : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hX
    have hsave := power_saving_to_log_saving (x := X) (β := 1 / 2)
      (lt_of_lt_of_le hx hX) hA' hδ
    have hlog : Real.log X ^ (-(A + k)) ≤ Real.log x ^ (-(A + k)) :=
      Real.rpow_le_rpow_of_nonpos hlx hlX (by linarith)
    have hconst : 0 ≤ (δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) := by
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by linarith) _)
    calc
      _ ≤ ((δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log X ^ (-(A + k))) *
          Real.log x ^ k := mul_le_mul_of_nonneg_right hsave (Real.rpow_nonneg hlx.le _)
      _ ≤ ((δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + k))) *
          Real.log x ^ k := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog hconst) (Real.rpow_nonneg hlx.le _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hlx]
        congr 2
        ring
  
  /- LEAF. Page 13, Case 2 i. The two mean squares control the pair,
  while the third norm is at most its length to one quarter.
  CONDITIONAL on the original three inputs. -/
  have neither_small_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ thirdNormPart (casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false)
        (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
        (X ^ (1 - α₁ - α₂)) true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)  := by
    intro B
    refine ⟨1, by norm_num, ?_⟩
    intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
    obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
    obtain ⟨Ce, K0, hCe, hK0, he⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
    let H := 2 * Cm * Ce
    let R := ((ε / 4) / (A + (K0 + 1))) ^ (-(A + (K0 + 1)))
    have hH : 0 < H := by dsimp [H]; positivity
    have hR : 0 ≤ R := by dsimp [R]; positivity
    refine ⟨H * R, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
    let M := X ^ α₁
    let N := X ^ α₂
    let L := X ^ (1 - α₁ - α₂)
    let Q : ℝ := (q : ℝ) * T
    let P := thirdNormPart (casePart S
      (fun p => dominanceFlag Q M (dirPoly a c₁ c₂ M p.2 (half p.1)))
      (fun p => dominanceFlag Q N (dirPoly b c₁ c₂ N p.2 (half p.1))) false false)
      (fun p => dirPoly e c₁ c₂ L p.2 (half p.1)) L true
    have hsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hx3 : 3 ≤ x := by linarith
    have hlx : 1 ≤ Real.log x := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
      linarith [Real.log_three_gt_d9]
    have hlx0 : 0 < Real.log x := by linarith
    have hXge : x ≤ X := by
      rcases hX with rfl | rfl
      · exact le_rfl
      · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
        calc
          x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
    have hX0 : 0 < X := by linarith
    have hX1 : 1 ≤ X := by linarith
    have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
    have hlog0 : 0 ≤ Real.log x ^ (K0 + 1) := Real.rpow_nonneg hlx0.le _
    by_cases hEmpty : P = ∅
    · change (∑ p ∈ P, _) ≤ _
      rw [hEmpty, Finset.sum_empty]
      positivity
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hcase := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hMQ : M < Q := nondominant_scale_lt (by dsimp [M]; linarith) hcase.1
    have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) hcase.2
    have hsp : WellSpaced P := by
      intro p hp p' hp' hne heq
      exact hspace p (hsub hp) p' (hsub hp') hne heq
    have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
    have hmoment (f : ℕ → ℂ) (F : ℝ) (hf : CoeffBound f B)
        (hF : 2 ≤ F) (hFx : F ≤ x) (hFQ : F ≤ Q) :
        (∑ p ∈ P, ‖dirPoly f c₁ c₂ F p.2 (half p.1)‖ ^ 2) ≤ H * Q * Real.log x ^ (K0 + 1) := by
      have hmF := hm x F T q P f hf hx hF hFx hT hTx hq hqx hsp htime
      have heF := he f hf x F hlx hF hFx
      have hEnonneg : 0 ≤ energy f c₁ c₂ F := Finset.sum_nonneg (fun n hn => by positivity)
      calc
        _ ≤ Cm * Real.log x * (Q + F) * energy f c₁ c₂ F := hmF
        _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by gcongr <;> linarith
        _ = H * Q * (Real.log x ^ K0 * Real.log x) := by dsimp [H]; ring
        _ = _ := by rw [Real.rpow_add hlx0, Real.rpow_one]
    have hpair := pair_of_square_bounds P
      (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
      (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hH.le hQ0 hQ0 hlog0
      (hmoment a M ha hM hMx hMQ.le) (hmoment b N hb hN hNx hNQ.le)
    have hpair' : (∑ p ∈ P,
        ‖dirPoly a c₁ c₂ M p.2 (half p.1) * dirPoly b c₁ c₂ N p.2 (half p.1)‖) ≤
        H * Q * Real.log x ^ (K0 + 1) := by
      apply hpair.trans_eq
      calc
        _ = H * (Real.sqrt Q * Real.sqrt Q) * Real.log x ^ (K0 + 1) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hQ0]
    have htriple := triple_of_pair_bound P
      (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
      (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
      (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
      (by dsimp [L]; positivity : 0 ≤ L ^ (1 / 4 : ℝ)) hpair'
      (by intro p hp; exact of_decide_eq_true (Finset.mem_filter.mp hp).2)
    have hpow : Q * L ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 - ε / 4) := by
      rw [show Q = X ^ (1 - θ) from hqT]
      dsimp [L]
      rw [← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      have hh := case2i_margin hgam
      linarith
    have hsave := power_saving_with_log (by linarith : 1 < x) hXge hA
      (by linarith : 0 < ε / 4) (by linarith : 0 ≤ K0 + 1)
    calc
      _ ≤ (H * Q * Real.log x ^ (K0 + 1)) * L ^ (1 / 4 : ℝ) := htriple
      _ = H * (Q * L ^ (1 / 4 : ℝ)) * Real.log x ^ (K0 + 1) := by ring
      _ ≤ H * X ^ (1 / 2 - ε / 4) * Real.log x ^ (K0 + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le) hlog0
      _ = H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ (K0 + 1)) := by ring
      _ ≤ H * (R * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_left hsave hH.le
      _ = _ := by ring
  
  have two_zpow_eq_rpow_level {X m : ℝ} (hX : 1 < X) (hm : 0 < m) (k : ℤ) :
      (2 : ℝ) ^ k = X ^ (m * ((1 / 2 + (k : ℝ) * Real.log 2 / (m * Real.log X)) - 1 / 2)) := by
    have hlX : 0 < Real.log X := Real.log_pos hX
    have hmX : m * Real.log X ≠ 0 := by positivity
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by linarith : (0 : ℝ) < X),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp
    ring
  
  /- The minimum of two powers of `X` at least one is the power of their minimum. -/
  have rpow_min_eq {X : ℝ} (hX : 1 ≤ X) {a b : ℝ} :
      min (X ^ a) (X ^ b) = X ^ min a b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, min_eq_left (Real.rpow_le_rpow_of_exponent_le hX h)]
    · rw [min_eq_right h, min_eq_right (Real.rpow_le_rpow_of_exponent_le hX h)]
  
  /- `(X ^ b) ^ n = X ^ (b * n)`. -/
  have rpow_pow_nat {X b : ℝ} (hX : 0 < X) (n : ℕ) : (X ^ b) ^ n = X ^ (b * n) := by
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero]
    | succ n ih => rw [pow_succ, ih, ← Real.rpow_add hX]; congr 1; push_cast; ring
  
  /- `1 / X ^ a = X ^ (-a)`. -/
  have one_div_rpow {X a : ℝ} (hX : 0 < X) : 1 / X ^ a = X ^ (-a) := by
    rw [show (1 : ℝ) = X ^ (0 : ℝ) from (Real.rpow_zero X).symm, ← Real.rpow_sub hX]
    congr 1
    ring
  
  /- The first displayed cardinality term of display 3.10 in the exponent scale. -/
  have level_first_term {X F V : ℝ} {m σ : ℝ} (hX : 0 < X) (_hm : 0 < m)
      (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) :
      F / V ^ 2 = X ^ (m * (2 - 2 * σ)) := by
    subst hF hV
    rw [rpow_pow_nat hX 2, ← Real.rpow_sub hX]
    congr 1
    ring
  
  /- The second displayed cardinality term of display 3.10 in the exponent scale, first alternative. -/
  have level_second_one {X V : ℝ} {m σ : ℝ} (hX : 0 < X) (_hm : 0 < m)
      (hV : V = X ^ (m * (σ - 1 / 2))) :
      1 / V ^ 2 = X ^ (m * (1 - 2 * σ)) := by
    subst hV
    rw [rpow_pow_nat hX 2, one_div_rpow hX]
    congr 1
    ring
  
  /- The second displayed cardinality term of display 3.10 in the exponent scale, second alternative. -/
  have level_second_six {X F V : ℝ} {m σ : ℝ} (hX : 0 < X) (_hm : 0 < m)
      (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) :
      F / V ^ 6 = X ^ (m * (4 - 6 * σ)) := by
    subst hF hV
    rw [rpow_pow_nat hX 6, ← Real.rpow_sub hX]
    congr 1
    ring
  
  /- The three cell levels combine into one power of `X`. -/
  have cell_level_mul {X : ℝ} (hX : 0 < X) {m n l σ1 σ2 σ3 : ℝ} {k1 k2 k3 : ℤ}
      (h1 : (2 : ℝ) ^ k1 = X ^ (m * (σ1 - 1 / 2)))
      (h2 : (2 : ℝ) ^ k2 = X ^ (n * (σ2 - 1 / 2)))
      (h3 : (2 : ℝ) ^ k3 = X ^ (l * (σ3 - 1 / 2))) :
      (2 : ℝ) ^ k1 * (2 : ℝ) ^ k2 * (2 : ℝ) ^ k3 =
        X ^ (m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + l * (σ3 - 1 / 2)) := by
    rw [h1, h2, h3, ← Real.rpow_add hX, ← Real.rpow_add hX]
  
  /- The exponent of a tiny-value contribution stays below one half. -/
  have tiny_exponent {θ ε m n l : ℝ} (hε : 0 < ε) (hεu : ε ≤ 1 / 2)
      (h38 : 1 / 2 + ε < θ) (h36 : |m - n| < 2 * θ - 1 - ε)
      (hθ : θ < 7 / 12) (h37 : l < Thm4.gam θ - ε) (hsum : m + n + l = 1) (hl : 0 < l) :
      (max m (1 - θ) + max (1 - θ) l) / 2 ≤ 1 / 2 - ε / 4 := by
    have hm_th : m < θ - ε / 2 := by
      have h1 := (abs_lt.mp h36).2
      linarith
    have hgam := Thm4.gam_le_one θ
    rcases le_or_gt m (1 - θ) with hm1 | hm1
    · rcases le_or_gt l (1 - θ) with hl1 | hl1
      · rw [max_eq_right hm1, max_eq_left hl1]; linarith
      · rw [max_eq_right hm1, max_eq_right hl1.le]; linarith
    · rcases le_or_gt l (1 - θ) with hl1 | hl1
      · rw [max_eq_left hm1.le, max_eq_left hl1]; linarith
      · rw [max_eq_left hm1.le, max_eq_right hl1.le]
        have hn : ε / 2 ≤ n := by
          by_contra hn
          push_neg at hn
          have hm2 : m < 2 * θ - 1 - ε / 2 := by
            have := (abs_lt.mp h36).2; linarith
          have : 2 - 2 * θ < l := by linarith
          linarith
        linarith
  
  /- The logarithmic allowance of display 3.10 combines with a coefficient-energy bound. -/
  have card_le_of_parts {R C Ce K e1 e2 Qterm E x X : ℝ}
      (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hE : 0 ≤ E) (hQterm : 0 ≤ Qterm)
      (hlog : 1 ≤ Real.log x) (hX : 1 ≤ X)
      (hcard : R ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm))
      (hEbd : E ≤ Ce * Real.log x ^ K) (hQ : Qterm ≤ X ^ e2) :
      R ≤ (C * (Ce + 16 * Ce ^ 3) * 4) * Real.log x ^ (2 + 3 * K) * X ^ max e1 e2 := by
    have hlx0 : 0 < Real.log x := by linarith
    have hcube : E + 16 * E ^ 3 ≤ (Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K) :=
      energy_cubic_log_bound hE hCe hK hlog hEbd
    have hEE : E + E ^ 3 ≤ (Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K) := by
      have := pow_nonneg hE 3
      nlinarith
    have hXE0 : 0 ≤ X ^ e1 := Real.rpow_nonneg (by linarith) _
    have hXmax : X ^ e1 + Qterm ≤ 2 * X ^ max e1 e2 := by
      have h1 : X ^ e1 ≤ X ^ max e1 e2 := Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _)
      have h2 : Qterm ≤ X ^ max e1 e2 := hQ.trans (Real.rpow_le_rpow_of_exponent_le hX (le_max_right _ _))
      linarith
    have hloglog : Real.log x + Real.log x ^ 2 ≤ 2 * Real.log x ^ 2 := by nlinarith
    have hlogpos : 0 ≤ Real.log x := le_trans (by norm_num) hlog
    have hcombine : (Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K) ≤
        2 * Real.log x ^ (2 + 3 * K) := by
      have h1 : (Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K) ≤
          (2 * Real.log x ^ 2) * Real.log x ^ (3 * K) :=
        mul_le_mul_of_nonneg_right hloglog (Real.rpow_nonneg hlogpos _)
      have h2 : (2 * Real.log x ^ 2) * Real.log x ^ (3 * K) = 2 * Real.log x ^ (2 + 3 * K) := by
        rw [Real.rpow_add hlx0, Real.rpow_two]
        ring
      linarith
    have hfin : (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
        (X ^ e1 + Qterm) ≤
        (C * (Ce + 16 * Ce ^ 3) * 4) * Real.log x ^ (2 + 3 * K) * X ^ max e1 e2 := by
      have hA : 0 ≤ C * (Ce + 16 * Ce ^ 3) := by positivity
      have h1 := mul_le_mul hcombine hXmax (by linarith) (by positivity)
      calc (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
          (X ^ e1 + Qterm)
          = (C * (Ce + 16 * Ce ^ 3)) * (((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
            (X ^ e1 + Qterm)) := by ring
        _ ≤ (C * (Ce + 16 * Ce ^ 3)) * ((2 * Real.log x ^ (2 + 3 * K)) *
            (2 * X ^ max e1 e2)) := mul_le_mul_of_nonneg_left h1 hA
        _ = _ := by ring
    have hstep : C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm) ≤
        (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
          (X ^ e1 + Qterm) := by
      have h1 : C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) ≤
          C * (Real.log x + Real.log x ^ 2) * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K)) := by
        apply mul_le_mul_of_nonneg_left hEE
        positivity
      calc C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm)
          = (C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3)) * (X ^ e1 + Qterm) := by ring
        _ ≤ (C * (Real.log x + Real.log x ^ 2) * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K))) *
              (X ^ e1 + Qterm) := mul_le_mul_of_nonneg_right h1 (by linarith)
        _ = _ := by ring
    calc R ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm) := hcard
      _ ≤ (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
            (X ^ e1 + Qterm) := hstep
      _ ≤ _ := hfin
  
  /- The three displayed cardinality terms of display 3.10 for a fixed power `g`. -/
  have level_pow_terms {X F V : ℝ} {l σ : ℝ} {g : ℕ} (hX : 0 < X)
      (hF : F = X ^ l) (hV : V = X ^ (l * (σ - 1 / 2))) :
      F ^ g / V ^ (2 * g) = X ^ ((g : ℝ) * l * (2 - 2 * σ)) ∧
      1 / V ^ (2 * g) = X ^ ((g : ℝ) * l * (1 - 2 * σ)) ∧
      F ^ g / V ^ (6 * g) = X ^ ((g : ℝ) * l * (4 - 6 * σ)) := by
    subst hF hV
    have h1 : (X ^ l) ^ g = X ^ (l * (g : ℝ)) := rpow_pow_nat hX g
    have h2 : (X ^ (l * (σ - 1 / 2))) ^ (2 * g) =
        X ^ ((l * (σ - 1 / 2)) * (2 * (g : ℝ))) := by
      rw [rpow_pow_nat hX (2 * g)]
      push_cast
      ring_nf
    have h6 : (X ^ (l * (σ - 1 / 2))) ^ (6 * g) =
        X ^ ((l * (σ - 1 / 2)) * (6 * (g : ℝ))) := by
      rw [rpow_pow_nat hX (6 * g)]
      push_cast
      ring_nf
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, h2, ← Real.rpow_sub hX]; congr 1; ring
    · rw [h2, one_div_rpow hX]; congr 1; ring
    · rw [h1, h6, ← Real.rpow_sub hX]; congr 1; ring
  
  /- Display 3.10, first power: the minimum-form second term is `qT` times `X` to `f` of sigma. -/
  have bracket_one {X F V Q θ m σ : ℝ} (hX : 0 < X) (hX1 : 1 ≤ X) (_hm : 0 < m)
      (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) (hQ : Q = X ^ (1 - θ)) :
      Q * min (1 / V ^ 2) (F / V ^ 6) ≤ X ^ (1 - θ + m * Thm4.f σ) := by
    have hmin : min (m * (1 - 2 * σ)) (m * (4 - 6 * σ)) = m * Thm4.f σ := by
      unfold Thm4.f
      rcases le_total (1 - 2 * σ) (4 - 6 * σ) with h | h
      · rw [min_eq_left h, min_eq_left (by nlinarith)]
      · rw [min_eq_right h, min_eq_right (by nlinarith)]
    rw [level_second_one hX _hm hV, level_second_six hX _hm hF hV, hQ, rpow_min_eq hX1,
      ← Real.rpow_add hX, hmin]
  
  /- Display 3.10, fixed power `g`: the second term is at most `qT` times its sixth-moment branch. -/
  have bracket_gen {X F V Q θ l σ : ℝ} {g : ℕ} (hX : 0 < X) (hX1 : 1 ≤ X)
      (_hl : 0 < l) (_hg : 1 ≤ g)
      (hF : F = X ^ l) (hV : V = X ^ (l * (σ - 1 / 2))) (hQ : Q = X ^ (1 - θ)) :
      Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) ≤
        X ^ (1 - θ + (g : ℝ) * l * (4 - 6 * σ)) := by
    obtain ⟨-, -, h6⟩ := level_pow_terms hX hF hV (g := g)
    have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
    have hmin := min_le_right (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))
    calc Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))
        ≤ Q * (F ^ g / V ^ (6 * g)) := mul_le_mul_of_nonneg_left hmin hQ0
      _ = X ^ (1 - θ) * X ^ ((g : ℝ) * l * (4 - 6 * σ)) := by rw [h6, hQ]
      _ = X ^ (1 - θ + (g : ℝ) * l * (4 - 6 * σ)) := by rw [← Real.rpow_add hX]
  
  /- A nonnegative factor distributes over a minimum. -/
  have mul_min_of_nonneg {a b c : ℝ} (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) := by
    rcases le_total b c with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  
  /- A cell's cardinality obeys the smallest of its three level-set bounds. -/
  have card_le_three_min {R C D s1 s2 s3 x X : ℝ}
      (hlog : 1 ≤ Real.log x) (hC : 0 ≤ C) (hX : 1 ≤ X)
      (h1 : R ≤ C * Real.log x ^ D * X ^ s1)
      (h2 : R ≤ C * Real.log x ^ D * X ^ s2)
      (h3 : R ≤ C * Real.log x ^ D * X ^ s3) :
      R ≤ C * Real.log x ^ D * X ^ min s1 (min s2 s3) := by
    have hCL : 0 ≤ C * Real.log x ^ D := by
      have : 0 ≤ Real.log x ^ D := Real.rpow_nonneg (le_trans (by norm_num) hlog) _
      positivity
    have hXs : X ^ min s1 (min s2 s3) = min (X ^ s1) (min (X ^ s2) (X ^ s3)) := by
      rw [rpow_min_eq hX, rpow_min_eq hX]
    have heq : C * Real.log x ^ D * X ^ min s1 (min s2 s3) =
        min (C * Real.log x ^ D * X ^ s1)
          (min (C * Real.log x ^ D * X ^ s2) (C * Real.log x ^ D * X ^ s3)) := by
      rw [hXs, mul_min_of_nonneg hCL, mul_min_of_nonneg hCL]
    rw [heq]
    exact le_min h1 (le_min h2 h3)
  
  /- Raise the constant and the logarithmic allowance of a cell bound. -/
  have card_le_weaken {R C Cg D Dg s x X : ℝ}
      (hlog : 1 ≤ Real.log x) (hC : 0 ≤ C) (hCg : C ≤ Cg) (hD : D ≤ Dg) (hX : 1 ≤ X)
      (h : R ≤ C * Real.log x ^ D * X ^ s) : R ≤ Cg * Real.log x ^ Dg * X ^ s := by
    have hL0 : 0 ≤ Real.log x ^ D := Real.rpow_nonneg (le_trans (by norm_num) hlog) _
    have hL : Real.log x ^ D ≤ Real.log x ^ Dg := Real.rpow_le_rpow_of_exponent_le hlog hD
    have hXs : 0 ≤ X ^ s := Real.rpow_nonneg (by linarith) _
    have hCg0 : 0 ≤ Cg := le_trans hC hCg
    have hLg0 : 0 ≤ Real.log x ^ Dg := Real.rpow_nonneg (le_trans (by norm_num) hlog) _
    calc R ≤ C * Real.log x ^ D * X ^ s := h
      _ ≤ Cg * Real.log x ^ Dg * X ^ s := by
          exact mul_le_mul (mul_le_mul hCg hL hL0 hCg0) le_rfl hXs (mul_nonneg hCg0 hLg0)
  
  /- The non-dominant tag, read at a dyadic cell level, forces the case-3 second length scale. -/
  have nondominant_exponent {X N Q θ n σ : ℝ} {z : ℂ} {k : ℤ}
      (hX : 1 < X) (hn : 0 < n) (hN : N = X ^ n) (hQ : Q = X ^ (1 - θ)) (hσ : 1 / 2 ≤ σ)
      (hV : (2 : ℝ) ^ k = X ^ (n * (σ - 1 / 2))) (hlevel : (2 : ℝ) ^ k ≤ ‖z‖)
      (hNQ : N < Q) (hz : dominanceFlag Q N z = false) :
      n * Thm4.c σ < 1 - θ := by
    have hX0 : 0 < X := by linarith
    have hlX : 0 < Real.log X := Real.log_pos hX
    have hN1 : 1 < N := by rw [hN]; exact Real.one_lt_rpow hX hn
    have hmax : ¬ (Q ≤ max N (‖z‖ ^ 4)) := by
      intro h
      exact (of_decide_eq_false hz) (by rw [dominance_power_eq_max hN1]; exact h)
    have hQgt : ‖z‖ ^ 4 < Q := by
      have h := not_le.mp (fun hc => hmax (le_trans hc (le_max_right _ _)))
      exact h
    have hlev4 : X ^ (4 * (n * (σ - 1 / 2))) ≤ ‖z‖ ^ 4 := by
      have hpow : (X ^ (n * (σ - 1 / 2))) ^ 4 = X ^ (4 * (n * (σ - 1 / 2))) := by
        rw [rpow_pow_nat hX0 4]; congr 1; ring
      rw [← hpow]
      exact pow_le_pow_left₀ (by positivity) (by rw [← hV]; exact hlevel) 4
    have h4 : 4 * (n * (σ - 1 / 2)) < 1 - θ := by
      have hlt : X ^ (4 * (n * (σ - 1 / 2))) < X ^ (1 - θ) := by
        rw [hQ] at hQgt
        exact lt_of_le_of_lt hlev4 hQgt
      have hlog := Real.log_lt_log (by positivity) hlt
      rw [Real.log_rpow hX0, Real.log_rpow hX0] at hlog
      exact lt_of_mul_lt_mul_right hlog hlX.le
    have hNQex : n < 1 - θ := by
      have hlt : X ^ n < X ^ (1 - θ) := by simpa only [hN, hQ] using hNQ
      have hlog := Real.log_lt_log (by positivity) hlt
      rw [Real.log_rpow hX0, Real.log_rpow hX0] at hlog
      exact lt_of_mul_lt_mul_right hlog hlX.le
    unfold Thm4.c
    split_ifs with h
    · linarith
    · nlinarith
  
  /- A dyadic cell sum costs at most the cube of the level count. -/
  have sum_over_cells {q : ℕ} {S : Finset (ℝ × DirichletCharacter ℂ q)}
      {f1 f2 f3 : ℝ × DirichletCharacter ℂ q → ℂ} {x V H Clev : ℝ}
      (hlog : 1 ≤ Real.log x) (hV : 0 < V) (hClev : 0 ≤ Clev) (hH : 0 ≤ H)
      (h1 : ∀ p ∈ S, 1 ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ V)
      (h2 : ∀ p ∈ S, 1 ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ V)
      (h3 : ∀ p ∈ S, 1 ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ V)
      (hcell : ∀ k ∈ dyadicLevels 1 V ×ˢ dyadicLevels 1 V ×ˢ dyadicLevels 1 V,
        (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤ H)
      (hlev : ((dyadicLevels 1 V).card : ℝ) ≤ Clev * Real.log x) :
      (∑ p ∈ S, ‖f1 p * f2 p * f3 p‖) ≤ (Clev * Real.log x) ^ 3 * H := by
    have hsum := dyadic_sum_bound S f1 f2 f3 (H := H) (v := 1) (V := V) one_pos h1 h2 h3 hcell
    have hcard0 : (0 : ℝ) ≤ ((dyadicLevels 1 V).card : ℝ) := Nat.cast_nonneg _
    have hcube : (((dyadicLevels 1 V).card : ℝ)) ^ 3 ≤ (Clev * Real.log x) ^ 3 :=
      pow_le_pow_left₀ hcard0 hlev 3
    exact hsum.trans (mul_le_mul_of_nonneg_right hcube hH)
  
  /- Display 3.10 at a dyadic cell level, in the exponent form the cell sum needs.
  One instantiation serves the first and second factors at `g = 1` and the third at the
  selected power `g`. -/
  have cell_card_of_level {q : ℕ} {S : Finset (ℝ × DirichletCharacter ℂ q)}
      {x X θ F V Q m σ e1 e2 : ℝ} {g : ℕ} {C Ce K E : ℝ}
      (hlog : 1 ≤ Real.log x) (hX1 : 1 ≤ X) (hm : 0 < m)
      (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) (hQ : Q = X ^ (1 - θ))
      (hFpos : 0 < F) (hVpos : 0 < V) (hV1 : 1 ≤ V)
      (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hE : 0 ≤ E)
      (hb1 : F ^ g / V ^ (2 * g) = X ^ e1)
      (hb2 : Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) ≤ X ^ e2)
      (hcard : (S.card : ℝ) ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) *
        (F ^ g / V ^ (2 * g) + Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))))
      (hEbd : E ≤ Ce * Real.log x ^ K) :
      (S.card : ℝ) ≤ (C * (Ce + 16 * Ce ^ 3) * 4) * Real.log x ^ (2 + 3 * K) * X ^ max e1 e2 := by
    have hQpos : 0 < Q := by rw [hQ]; positivity
    have hinner : 0 < min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) :=
      lt_min (by positivity) (by positivity)
    have hQn : 0 ≤ Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) := le_of_lt (mul_pos hQpos hinner)
    exact card_le_of_parts (R := (S.card : ℝ)) (C := C) (Ce := Ce) (K := K) (e1 := e1)
      (e2 := e2) (Qterm := Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) (E := E)
      (x := x) (X := X) hC hCe hK hE hQn hlog hX1 (by simpa only [← hb1] using hcard) hEbd hb2
  
  /- Where one of the first two factors is at most one, the mean squares of the three
  factors and the exponent inequality `tiny_exponent` give the whole contribution. -/
  have tiny_final {q : ℕ} {P TIN : Finset (ℝ × DirichletCharacter ℂ q)}
      {f1 f2 f3 : ℝ × DirichletCharacter ℂ q → ℂ} {x X ε D HB a b e : ℝ}
      (hlog : 1 ≤ Real.log x) (hX1 : 1 ≤ X) (hHB : 0 ≤ HB) (hD : 0 ≤ D) (hε : 0 < ε)
      (hsub : TIN ⊆ P)
      (htiny : ∀ p ∈ TIN, ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1)
      (hA : (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ HB * X ^ a * Real.log x ^ D)
      (hB : (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ HB * X ^ b * Real.log x ^ D)
      (hE : (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ HB * X ^ e * Real.log x ^ D)
      (hexp : max a b + e ≤ 1 - ε / 2) :
      (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ≤ (4 * HB) * Real.log x ^ D * X ^ (1 / 2 - ε / 4) := by
    have hlx0 : 0 < Real.log x := lt_of_lt_of_le one_pos hlog
    -- one of the first two factors is at most one, so it costs nothing
    have hstep : ∀ p ∈ TIN, ‖f1 p * f2 p * f3 p‖ ≤ max ‖f1 p‖ ‖f2 p‖ * ‖f3 p‖ := by
      intro p hp
      rw [norm_mul, norm_mul]
      have h3 : (0 : ℝ) ≤ ‖f3 p‖ := norm_nonneg _
      rcases htiny p hp with h | h
      · have : ‖f1 p‖ * ‖f2 p‖ ≤ max ‖f1 p‖ ‖f2 p‖ := by
          calc ‖f1 p‖ * ‖f2 p‖ ≤ 1 * ‖f2 p‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
            _ = ‖f2 p‖ := one_mul _
            _ ≤ _ := le_max_right _ _
        exact mul_le_mul_of_nonneg_right this h3
      · have : ‖f1 p‖ * ‖f2 p‖ ≤ max ‖f1 p‖ ‖f2 p‖ := by
          calc ‖f1 p‖ * ‖f2 p‖ ≤ ‖f1 p‖ * 1 := mul_le_mul_of_nonneg_left h (norm_nonneg _)
            _ = ‖f1 p‖ := mul_one _
            _ ≤ _ := le_max_left _ _
        exact mul_le_mul_of_nonneg_right this h3
    -- Cauchy-Schwarz for the pair of first factors against the third
    have hS2 : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ^ 2 ≤
        (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2) * (∑ p ∈ TIN, ‖f3 p‖ ^ 2) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq TIN
        (fun p => max ‖f1 p‖ ‖f2 p‖) (fun p => ‖f3 p‖)
      calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ^ 2
          ≤ (∑ p ∈ TIN, max ‖f1 p‖ ‖f2 p‖ * ‖f3 p‖) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => norm_nonneg _))
              (Finset.sum_le_sum hstep) 2
        _ ≤ _ := hcs
    have hmax2 : (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2) ≤
        HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D := by
      have hpt : ∀ p ∈ P, (max ‖f1 p‖ ‖f2 p‖) ^ 2 ≤ ‖f1 p‖ ^ 2 + ‖f2 p‖ ^ 2 := by
        intro p _
        rcases le_total ‖f1 p‖ ‖f2 p‖ with h | h
        · rw [max_eq_right h]; nlinarith [sq_nonneg ‖f1 p‖]
        · rw [max_eq_left h]; nlinarith [sq_nonneg ‖f2 p‖]
      have hmono1 : (∑ p ∈ TIN, ‖f1 p‖ ^ 2) ≤ ∑ p ∈ P, ‖f1 p‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
      have hmono2 : (∑ p ∈ TIN, ‖f2 p‖ ^ 2) ≤ ∑ p ∈ P, ‖f2 p‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
      calc (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2)
          ≤ ∑ p ∈ TIN, (‖f1 p‖ ^ 2 + ‖f2 p‖ ^ 2) :=
            Finset.sum_le_sum (fun p hp => hpt p (hsub hp))
        _ = (∑ p ∈ TIN, ‖f1 p‖ ^ 2) + ∑ p ∈ TIN, ‖f2 p‖ ^ 2 := Finset.sum_add_distrib
        _ ≤ _ := add_le_add (hmono1.trans hA) (hmono2.trans hB)
    have hEmono : (∑ p ∈ TIN, ‖f3 p‖ ^ 2) ≤ HB * X ^ e * Real.log x ^ D :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans hE
    -- the product of the two bounds is below the square of the target
    have hXmax : X ^ a + X ^ b ≤ 2 * X ^ max a b := by
      have h1 : X ^ a ≤ X ^ max a b := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
      have h2 : X ^ b ≤ X ^ max a b := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
      linarith
    have hlog2 : Real.log x ^ D * Real.log x ^ D = Real.log x ^ (D + D) :=
      (Real.rpow_add hlx0 _ _).symm
    have hXe : X ^ max a b * X ^ e = X ^ (max a b + e) := (Real.rpow_add (by linarith : (0:ℝ) < X) _ _).symm
    have hXfin : X ^ (max a b + e) ≤ X ^ (1 - ε / 2) := Real.rpow_le_rpow_of_exponent_le hX1 hexp
    have hR2 : (4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4)) ^ 2 =
        16 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (1 - ε / 2) := by
      have h1 : (X ^ (1 / 2 - ε / 4)) ^ 2 = X ^ (2 * (1 / 2 - ε / 4)) := by
        rw [rpow_pow_nat (by linarith : (0:ℝ) < X) 2]; congr 1; ring
      have h2 : (Real.log x ^ D) ^ 2 = Real.log x ^ (D + D) := by
        rw [rpow_pow_nat hlx0 2]; congr 1; ring
      rw [mul_pow, mul_pow, mul_pow, h1, h2]
      ring_nf
    have hprod : (HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D) *
        (HB * X ^ e * Real.log x ^ D) ≤
        (4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4)) ^ 2 := by
      rw [hR2]
      have hXp : 0 ≤ X ^ max a b := Real.rpow_nonneg (by linarith) _
      have hexp0 : 0 ≤ X ^ e := Real.rpow_nonneg (by linarith) _
      have hlogD : 0 ≤ Real.log x ^ D := Real.rpow_nonneg hlx0.le _
      have h1 : HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D ≤
          2 * HB * Real.log x ^ D * X ^ max a b := by
        have := mul_le_mul_of_nonneg_left hXmax (by positivity : (0:ℝ) ≤ HB * Real.log x ^ D)
        nlinarith
      have h2 : (2 * HB * Real.log x ^ D * X ^ max a b) * (HB * X ^ e * Real.log x ^ D) =
          2 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (max a b + e) := by
        rw [← hlog2, ← hXe]; ring
      have h3 : 2 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (max a b + e) ≤
          16 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (1 - ε / 2) := by
        have := mul_le_mul_of_nonneg_left hXfin (by positivity : (0:ℝ) ≤ Real.log x ^ (D + D))
        have hHB2 : 0 ≤ HB ^ 2 := sq_nonneg HB
        nlinarith
      calc (HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D) *
            (HB * X ^ e * Real.log x ^ D)
          ≤ (2 * HB * Real.log x ^ D * X ^ max a b) * (HB * X ^ e * Real.log x ^ D) := by
            apply mul_le_mul_of_nonneg_right h1
            exact mul_nonneg (mul_nonneg hHB (by positivity)) (by positivity)
        _ = _ := h2
        _ ≤ _ := h3
    have hmid : (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2) * (∑ p ∈ TIN, ‖f3 p‖ ^ 2) ≤
        (HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D) *
          (HB * X ^ e * Real.log x ^ D) :=
      mul_le_mul hmax2 hEmono (Finset.sum_nonneg (fun p _ => by positivity)) (by positivity)
    have hfin : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ^ 2 ≤
        (4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4)) ^ 2 :=
      hS2.trans (hmid.trans hprod)
    have hS0 : (0 : ℝ) ≤ ∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖ :=
      Finset.sum_nonneg (fun p _ => norm_nonneg _)
    have hR0 : (0 : ℝ) ≤ 4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4) := by positivity
    nlinarith [hfin, hS0, hR0]
  
  /- One dyadic cell, once its cardinality is below `X ^ s` and the classification has put
  `s + E` below one half minus `ε/72`, contributes that much. -/
  have cell_sum_combine {q : ℕ} (S : Finset (ℝ × DirichletCharacter ℂ q))
      (f1 f2 f3 : ℝ × DirichletCharacter ℂ q → ℂ) (k : ℤ × ℤ × ℤ)
      {x X s E Ccell Dcell ε : ℝ} (hX0 : 0 < X) (hX1 : 1 ≤ X) (hε : 0 < ε)
      (hCcell : 0 ≤ Ccell) (hlog : 1 ≤ Real.log x)
      (hpos : ∀ p ∈ S, 0 < ‖f1 p‖ ∧ 0 < ‖f2 p‖ ∧ 0 < ‖f3 p‖)
      (hcard : ((dyadicCell S f1 f2 f3 k).card : ℝ) ≤ Ccell * Real.log x ^ Dcell * X ^ s)
      (hlevels : 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 = 8 * X ^ E)
      (hclass : s + E ≤ 1 / 2 - ε / 72) :
      (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤
        8 * Ccell * Real.log x ^ Dcell * X ^ (1 / 2 - ε / 72) := by
    have hcell := dyadic_cell_sum_le S f1 f2 f3 k hpos
    have hmul : ((dyadicCell S f1 f2 f3 k).card : ℝ) *
        (8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) ≤
        (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E) := by
      rw [hlevels]
      exact mul_le_mul hcard (le_refl _) (by positivity) (by positivity)
    have heq : (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E) =
        8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) := by
      calc (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E)
          = 8 * (Ccell * Real.log x ^ Dcell) * (X ^ s * X ^ E) := by ring
        _ = 8 * (Ccell * Real.log x ^ Dcell) * X ^ (s + E) := by rw [Real.rpow_add hX0]
        _ = 8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) := by ring
    have hstep : X ^ (s + E) ≤ X ^ (1 / 2 - ε / 72) :=
      Real.rpow_le_rpow_of_exponent_le hX1 hclass
    have hfin : 8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) ≤
        8 * Ccell * Real.log x ^ Dcell * X ^ (1 / 2 - ε / 72) := by
      apply mul_le_mul_of_nonneg_left hstep
      positivity
    calc (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖)
        ≤ ((dyadicCell S f1 f2 f3 k).card : ℝ) *
            (8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) := hcell
      _ ≤ (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E) := hmul
      _ = 8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) := heq
      _ ≤ _ := hfin
  
  
  /- LEAF. Page 13, Case 2 ii, display 3.13 and the two following bounds.
  Only the part above the third norm threshold remains. Apply the sixth
  polynomial power bound and its two interpolation weights. OPEN.
  CONDITIONAL on the original three inputs. -/
  have neither_large_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ thirdNormPart (casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false)
        (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
        (X ^ (1 - α₁ - α₂)) false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    intro B
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro ε hε hεu' c₁ c₂ hc₁ hc₂ Kfun A hA
    have hεu : ε ≤ 1 / 2 := le_of_lt hεu'
    -- ## constants, all named before `θ`
    obtain ⟨Cn, hCn, hnorm⟩ := dirPoly_norm_uniform B c₁ c₂ hc₁ (hc₁.trans hc₂)
    have hCn1 : 0 < max Cn 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    obtain ⟨g0', hg0'1, hcut'⟩ := exists_uniform_power_cutoff hε
    let g0 : ℕ := max g0' 3
    have hg0 : 3 ≤ g0 := le_max_right _ _
    have hg01 : 1 ≤ g0 := le_trans hg0'1 (le_max_left _ _)
    have hlevel_pkg : ∀ g : ℕ, 1 ≤ g → ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
        ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
        CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        0 < V → WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖dirPoly a c₁ c₂ F p.2 (half p.1)‖) →
        (let E := energy (truncatedCoeffs a c₁ c₂ F ^ g).coeff (c₁ ^ g) (c₂ ^ g) (F ^ g);
          (S.card : ℝ) ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) *
            (F ^ g / V ^ (2 * g) +
              (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)))) := by
      intro g hg
      exact power_level_min hmean hlarge B c₁ c₂ hc₁ hc₂ g hg
    choose Cpm hCpmpos hCpm using hlevel_pkg
    have henergy_pkg : ∀ g : ℕ, 1 ≤ g → ∃ Ce K : ℝ, 0 < Ce ∧ 0 ≤ K ∧
        ∀ f : ℕ → ℂ, CoeffBound f ((g : ℝ) * (max B 0 + 1)) → ∀ x F : ℝ,
          1 ≤ Real.log x → 2 ≤ F → F ≤ x →
          energy f (c₁ ^ g) (c₂ ^ g) F ≤ Ce * Real.log x ^ K := by
      intro g hg
      exact energy_log_uniform henergy ((g : ℝ) * (max B 0 + 1)) (c₁ ^ g) (c₂ ^ g)
        (pow_pos hc₁ g) (pow_lt_pow_left₀ hc₂ hc₁.le (by omega))
    choose Cem Kem hCempos hKem hEn using henergy_pkg
    obtain ⟨Cd, Dd, hCd, hDd, hd⟩ :=
      dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
    obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
    obtain ⟨Ce, K0, hCe, hK0, hen⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
    let Cfam : ℕ → ℝ := fun g => if h : 1 ≤ g then Cpm g h else 1
    let Cefam : ℕ → ℝ := fun g => if h : 1 ≤ g then Cem g h * max 1 ((g0 : ℝ) ^ Kem g h) else 1
    let Kfam : ℕ → ℝ := fun g => if h : 1 ≤ g then Kem g h else 0
    have hCfam : ∀ g (hg : 1 ≤ g), Cfam g = Cpm g hg := fun g hg => by
      dsimp [Cfam]; rw [dif_pos hg]
    have hCefam : ∀ g (hg : 1 ≤ g),
        Cefam g = Cem g hg * max 1 ((g0 : ℝ) ^ Kem g hg) := fun g hg => by
      dsimp [Cefam]; rw [dif_pos hg]
    have hKfam : ∀ g (hg : 1 ≤ g), Kfam g = Kem g hg := fun g hg => by
      dsimp [Kfam]; rw [dif_pos hg]
    have hCfam0 : ∀ g, 1 ≤ g → 0 < Cfam g := fun g hg => by
      rw [hCfam g hg]; exact hCpmpos g hg
    have hCefam0 : ∀ g, 1 ≤ g → 0 < Cefam g := fun g hg => by
      rw [hCefam g hg]
      exact mul_pos (hCempos g hg) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hKfam0 : ∀ g, 1 ≤ g → 0 ≤ Kfam g := fun g hg => by
      rw [hKfam g hg]; exact hKem g hg
    let Cf : ℕ → ℝ := fun g => Cfam g * (Cefam g + 16 * Cefam g ^ 3) * 4
    let Df : ℕ → ℝ := fun g => 2 + 3 * Kfam g
    have hCf0 : ∀ g, 1 ≤ g → 0 ≤ Cf g := fun g hg => by
      have h1 := (hCfam0 g hg).le
      have h2 : 0 ≤ Cefam g + 16 * Cefam g ^ 3 := by
        have := (hCefam0 g hg).le; positivity
      dsimp [Cf]; positivity
    have hDf0 : ∀ g, 1 ≤ g → 0 ≤ Df g := fun g hg => by
      have := hKfam0 g hg; dsimp [Df]; linarith
    let Sg : Finset ℕ := Finset.Icc 1 g0
    have hSgne : Sg.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩⟩
    let Cst : ℝ := ∑ g ∈ Sg, Cf g
    let Dsum : ℝ := ∑ g ∈ Sg, Df g
    let Dst : ℝ := Dsum + Dd + (K0 + 1) + 2
    have hCst0 : 0 ≤ Cst :=
      Finset.sum_nonneg (fun g hg => hCf0 g (Finset.mem_Icc.mp hg).1)
    have hDsum0 : 0 ≤ Dsum :=
      Finset.sum_nonneg (fun g hg => hDf0 g (Finset.mem_Icc.mp hg).1)
    have hDst0 : 0 ≤ Dst := by dsimp [Dst]; linarith
    have hCf_le : ∀ g ∈ Sg, Cf g ≤ Cst := fun g hg =>
      Finset.single_le_sum (fun i hi => hCf0 i (Finset.mem_Icc.mp hi).1) hg
    have hDf_le : ∀ g ∈ Sg, Df g ≤ Dst := fun g hg => by
      have h1 : Df g ≤ Dsum :=
        Finset.single_le_sum (fun i hi => hDf0 i (Finset.mem_Icc.mp hi).1) hg
      have h2 : 0 ≤ Dd := hDd
      have h3 : 0 ≤ K0 + 1 := by linarith
      dsimp [Dst]; linarith
    have hDd_le : Dd ≤ Dst := by dsimp [Dst]; linarith
    have hK0_le : K0 + 1 ≤ Dst := by dsimp [Dst]; linarith [hDd]
    have h2_le : (2 : ℝ) ≤ Dst := by dsimp [Dst]; linarith [hDd, hK0]
    let Clev : ℝ := (Real.log (max Cn 1) + 2) / Real.log 2 + 2
    let H : ℝ := Cd + 2 * Cm * Ce + Cn + 1
    have hCmCe : 2 * Cm * Ce ≤ H := by dsimp [H]; nlinarith [hCd, hCn]
    have hHd : Cd ≤ H := by dsimp [H]; nlinarith [hCm, hCe, hCn]
    have hHn : Cn ≤ H := by dsimp [H]; nlinarith [hCd, hCm, hCe]
    have hH0 : 0 < H := lt_of_lt_of_le hCd hHd
    have hClev0 : 0 ≤ Clev := by
      have h1 : 0 ≤ Real.log (max Cn 1) := Real.log_nonneg (le_max_right _ _)
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      dsimp [Clev]; positivity
    let R1 : ℝ := ((ε / 4) / (A + Dst)) ^ (-(A + Dst))
    let R2 : ℝ := ((ε / 72) / (A + (3 + Dst))) ^ (-(A + (3 + Dst)))
    have hR10 : 0 ≤ R1 := Real.rpow_nonneg (by positivity) _
    have hR20 : 0 ≤ R2 := Real.rpow_nonneg (by positivity) _
    refine ⟨4 * H * R1 + 8 * Cst * Clev ^ 3 * R2, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
    let M : ℝ := X ^ α₁
    let N : ℝ := X ^ α₂
    let L : ℝ := X ^ (1 - α₁ - α₂)
    let Q : ℝ := (q : ℝ) * T
    let f1 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly a c₁ c₂ M p.2 (half p.1)
    let f2 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly b c₁ c₂ N p.2 (half p.1)
    let f3 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly e c₁ c₂ L p.2 (half p.1)
    let P : Finset (ℝ × DirichletCharacter ℂ q) := thirdNormPart (casePart S
      (fun p => dominanceFlag Q M (f1 p))
      (fun p => dominanceFlag Q N (f2 p)) false false) f3 L false
    have hx3 : 3 ≤ x := by linarith
    have hlx : 1 ≤ Real.log x := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
      linarith [Real.log_three_gt_d9]
    have hlx0 : 0 < Real.log x := by linarith
    have hXge : x ≤ X := by
      rcases hX with rfl | rfl
      · exact le_rfl
      · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
        calc
          x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
    have hX0 : 0 < X := by linarith
    have hX1 : 1 ≤ X := by linarith
    have hXlt : 1 < X := by linarith
    have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
    have hQ : Q = X ^ (1 - θ) := hqT
    have hθ5 : θ ≤ 3 / 5 := by linarith
    have hcut : θ - ε / 2 < Thm4.d θ g0 :=
      (hcut' θ (by linarith) (by linarith)).trans_le
        (Thm4.d_mono (by linarith) (Nat.cast_nonneg _) (by exact_mod_cast le_max_left g0' 3))
    have hα₁ : 0 < α₁ := by
      rcases le_or_gt α₁ 0 with h | h
      · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
      · exact h
    have hα₂ : 0 < α₂ := by
      rcases le_or_gt α₂ 0 with h | h
      · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
      · exact h
    have hl : 0 < 1 - α₁ - α₂ := by
      rcases le_or_gt (1 - α₁ - α₂) 0 with h | h
      · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
      · exact h
    have hml : 0 ≤ 1 - α₁ - α₂ := hl.le
    have hM0 : 0 < M := by dsimp [M]; positivity
    have hN0 : 0 < N := by dsimp [N]; positivity
    have hL0 : 0 < L := by dsimp [L]; positivity
    have hL1 : 1 ≤ L := by linarith
    have hmsum : α₁ + α₂ + (1 - α₁ - α₂) = 1 := by ring
    have hLQ : L ≤ Q := by
      rw [hQ]
      dsimp [L]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      have hg1 := Thm4.gam_le_one θ
      nlinarith
    have hmemP : ∀ p ∈ P, dominanceFlag Q M (f1 p) = false ∧
        dominanceFlag Q N (f2 p) = false ∧ L ^ (1 / 4 : ℝ) < ‖f3 p‖ := by
      intro p hp
      have h1 := (Finset.mem_filter.mp hp).1
      exact ⟨(Finset.mem_filter.mp h1).2.1, (Finset.mem_filter.mp h1).2.2,
        not_le.mp (of_decide_eq_false (Finset.mem_filter.mp hp).2)⟩
    have hPsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hsp : WellSpaced P := by
      intro p hp p' hp' hne heq
      exact hspace p (hPsub hp) p' (hPsub hp') hne heq
    have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hPsub hp)
    have hf3big : ∀ p ∈ P, 1 ≤ ‖f3 p‖ := by
      intro p hp
      have h := (hmemP p hp).2.2
      have h1 : (1 : ℝ) ≤ L ^ (1 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith
    have hgoal : (∑ p ∈ P, ‖f1 p * f2 p * f3 p‖) ≤
        (4 * H * R1 + 8 * Cst * Clev ^ 3 * R2) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
      by_cases hEmpty : P = ∅
      · rw [hEmpty, Finset.sum_empty]; positivity
      obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) (hmemP p₀ hp₀).2.1
      have hMQ : M < Q := nondominant_scale_lt (by dsimp [M]; linarith) (hmemP p₀ hp₀).1
      have hlogD : ∀ {d : ℝ}, d ≤ Dst → Real.log x ^ d ≤ Real.log x ^ Dst :=
        fun hd' => Real.rpow_le_rpow_of_exponent_le hlx hd'
      have hmomentM : (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
        have hh := hm x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
        have hQM : Q + M ≤ 2 * Q := by linarith
        have heM : energy a c₁ c₂ M ≤ Ce * Real.log x ^ K0 := hen a ha x M hlx hM hMx
        have hEnn : 0 ≤ energy a c₁ c₂ M := Finset.sum_nonneg (fun n hn => by positivity)
        have hstep : Cm * Real.log x * (Q + M) * energy a c₁ c₂ M ≤
            Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
          have h1 : 0 ≤ Cm * Real.log x := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hQM h1) heM hEnn (by positivity)
        have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
          rw [Real.rpow_add hlx0, Real.rpow_one]
        have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
            H * Q * Real.log x ^ Dst := by
          have h1 : 2 * Cm * Ce ≤ H := hCmCe
          have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0_le
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
            (Real.rpow_nonneg hlx0.le _) (by positivity)
        calc (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ Cm * Real.log x * (Q + M) * energy a c₁ c₂ M := hh
          _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
          _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
          _ ≤ H * Q * Real.log x ^ Dst := hfin
          _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
      have hmomentN : (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
        have hh := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
        have hQN : Q + N ≤ 2 * Q := by linarith
        have heN : energy b c₁ c₂ N ≤ Ce * Real.log x ^ K0 := hen b hb x N hlx hN hNx
        have hEnn : 0 ≤ energy b c₁ c₂ N := Finset.sum_nonneg (fun n hn => by positivity)
        have hstep : Cm * Real.log x * (Q + N) * energy b c₁ c₂ N ≤
            Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
          have h1 : 0 ≤ Cm * Real.log x := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hQN h1) heN hEnn (by positivity)
        have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
          rw [Real.rpow_add hlx0, Real.rpow_one]
        have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
            H * Q * Real.log x ^ Dst := by
          have h1 : 2 * Cm * Ce ≤ H := hCmCe
          have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0_le
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
            (Real.rpow_nonneg hlx0.le _) (by positivity)
        calc (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ Cm * Real.log x * (Q + N) * energy b c₁ c₂ N := hh
          _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
          _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
          _ ≤ H * Q * Real.log x ^ Dst := hfin
          _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
      have hmomentE : (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
        have hh := hm x L T q P e hecoeff hx hL hLx hT hTx hq hqx hsp htime
        have hQL : Q + L ≤ 2 * Q := by linarith
        have heL : energy e c₁ c₂ L ≤ Ce * Real.log x ^ K0 := hen e hecoeff x L hlx hL hLx
        have hEnn : 0 ≤ energy e c₁ c₂ L := Finset.sum_nonneg (fun n hn => by positivity)
        have hstep : Cm * Real.log x * (Q + L) * energy e c₁ c₂ L ≤
            Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
          have h1 : 0 ≤ Cm * Real.log x := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hQL h1) heL hEnn (by positivity)
        have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
          rw [Real.rpow_add hlx0, Real.rpow_one]
        have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
            H * Q * Real.log x ^ Dst := by
          have h1 : 2 * Cm * Ce ≤ H := hCmCe
          have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0_le
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
            (Real.rpow_nonneg hlx0.le _) (by positivity)
        calc (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ Cm * Real.log x * (Q + L) * energy e c₁ c₂ L := hh
          _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
          _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
          _ ≤ H * Q * Real.log x ^ Dst := hfin
          _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
      -- ## the large-value part over the dyadic cells
      let TIN : Finset (ℝ × DirichletCharacter ℂ q) := P.filter (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1)
      let MAIN : Finset (ℝ × DirichletCharacter ℂ q) :=
        P.filter (fun p => ¬ (‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1))
      have hTINsub : TIN ⊆ P := Finset.filter_subset _ _
      have hMAINsub : MAIN ⊆ P := Finset.filter_subset _ _
      have hsplit : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) +
          (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖) = ∑ p ∈ P, ‖f1 p * f2 p * f3 p‖ :=
        Finset.sum_filter_add_sum_filter_not P (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1) _
      have hexptiny : max (1 - θ) (1 - θ) + (1 - θ) ≤ 1 - ε / 2 := by
        rw [max_self]
        linarith
      have htinyA : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ≤
          4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
        have hbase := tiny_final (q := q) (P := P) (TIN := TIN) (f1 := f1) (f2 := f2) (f3 := f3)
          (x := x) (X := X) (ε := ε) (D := Dst) (HB := H) (a := 1 - θ) (b := 1 - θ) (e := 1 - θ)
          hlx hX1 hH0.le hDst0 hε hTINsub (fun p hp => (Finset.mem_filter.mp hp).2)
          hmomentM hmomentN hmomentE hexptiny
        have hsave1 : X ^ (1 / 2 - ε / 4) * Real.log x ^ Dst ≤
            R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
          power_saving_with_log (x := x) (X := X) (A := A) (δ := ε / 4) (k := Dst)
            (by linarith) hXge hA (by linarith) hDst0
        calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖)
            ≤ 4 * H * Real.log x ^ Dst * X ^ (1 / 2 - ε / 4) := hbase
          _ = 4 * H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ Dst) := by ring
          _ ≤ 4 * H * (R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
              mul_le_mul_of_nonneg_left hsave1 (by positivity)
          _ = 4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
      have hMAINA : (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖) ≤
          8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
        have hV1 : 1 ≤ max Cn 1 * x ^ 2 := by
          have h1 : 1 ≤ max Cn 1 := le_max_right _ _
          have h2 : 1 ≤ x ^ 2 := one_le_pow₀ (by linarith)
          exact one_le_mul_of_one_le_of_one_le h1 h2
        have hbig1 : ∀ p ∈ MAIN, 1 ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ max Cn 1 * x ^ 2 := by
          intro p hp
          have hntiny := (Finset.mem_filter.mp hp).2
          push_neg at hntiny
          refine ⟨le_of_lt hntiny.1, ?_⟩
          have hb1 := hnorm a ha M (by linarith : 1 ≤ M) q p.2 p.1
          have hMx2 : M ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hM0.le hMx 2
          calc ‖f1 p‖ ≤ Cn * M ^ 2 := hb1
            _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hMx2 hCn.le
            _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hbig2 : ∀ p ∈ MAIN, 1 ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ max Cn 1 * x ^ 2 := by
          intro p hp
          have hntiny := (Finset.mem_filter.mp hp).2
          push_neg at hntiny
          refine ⟨le_of_lt hntiny.2, ?_⟩
          have hb2 := hnorm b hb N (by linarith : 1 ≤ N) q p.2 p.1
          have hNx2 : N ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hN0.le hNx 2
          calc ‖f2 p‖ ≤ Cn * N ^ 2 := hb2
            _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hNx2 hCn.le
            _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hbig3 : ∀ p ∈ MAIN, 1 ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ max Cn 1 * x ^ 2 := by
          intro p hp
          refine ⟨hf3big p (hMAINsub hp), ?_⟩
          have hb3 := hnorm e hecoeff L (by linarith : 1 ≤ L) q p.2 p.1
          have hLx2 : L ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hL0.le hLx 2
          calc ‖f3 p‖ ≤ Cn * L ^ 2 := hb3
            _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hLx2 hCn.le
            _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hClev' : ((dyadicLevels 1 (max Cn 1 * x ^ 2)).card : ℝ) ≤ Clev * Real.log x :=
          quadratic_level_count (le_max_right _ _) (by linarith) hlx
        have hzp : ∀ j : ℤ, 0 ≤ j → (1 : ℝ) ≤ (2 : ℝ) ^ j := by
          intro j hj
          rw [← zpow_zero (2 : ℝ)]
          exact zpow_le_zpow_right₀ (by norm_num) hj
        -- the energy of a fixed power at the enlarged ambient point
        have hamb : ∀ (g : ℕ) (hg : 1 ≤ g) (F : ℝ), 2 ≤ F → F ≤ x →
            1 ≤ Real.log (x ^ g) := by
          intro g hg F hF hFx
          rw [Real.log_pow]
          have h1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
          nlinarith
        have hcell : ∀ k ∈ dyadicLevels 1 (max Cn 1 * x ^ 2) ×ˢ dyadicLevels 1 (max Cn 1 * x ^ 2) ×ˢ
            dyadicLevels 1 (max Cn 1 * x ^ 2),
            (∑ p ∈ dyadicCell MAIN f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤
              8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72) := by
          intro k hk
          obtain ⟨hk1, hk23⟩ := Finset.mem_product.mp hk
          obtain ⟨hk2, hk3⟩ := Finset.mem_product.mp hk23
          have hk1nn : (0 : ℤ) ≤ k.1 := by
            have h := (Finset.mem_Icc.mp hk1).1
            rwa [Int.log_one_right] at h
          have hk2nn : (0 : ℤ) ≤ k.2.1 := by
            have h := (Finset.mem_Icc.mp hk2).1
            rwa [Int.log_one_right] at h
          have hk3nn : (0 : ℤ) ≤ k.2.2 := by
            have h := (Finset.mem_Icc.mp hk3).1
            rwa [Int.log_one_right] at h
          let V1 : ℝ := (2 : ℝ) ^ k.1
          let V2 : ℝ := (2 : ℝ) ^ k.2.1
          let V3 : ℝ := (2 : ℝ) ^ k.2.2
          have hV1ge : (1 : ℝ) ≤ V1 := by simpa only [V1] using hzp k.1 hk1nn
          have hV2ge : (1 : ℝ) ≤ V2 := by simpa only [V2] using hzp k.2.1 hk2nn
          have hV3ge : (1 : ℝ) ≤ V3 := by simpa only [V3] using hzp k.2.2 hk3nn
          have hV1pos : 0 < V1 := lt_of_lt_of_le zero_lt_one hV1ge
          have hV2pos : 0 < V2 := lt_of_lt_of_le zero_lt_one hV2ge
          have hV3pos : 0 < V3 := lt_of_lt_of_le zero_lt_one hV3ge
          let σ1 : ℝ := 1 / 2 + (k.1 : ℝ) * Real.log 2 / (α₁ * Real.log X)
          let σ2 : ℝ := 1 / 2 + (k.2.1 : ℝ) * Real.log 2 / (α₂ * Real.log X)
          let σ3 : ℝ := 1 / 2 + (k.2.2 : ℝ) * Real.log 2 / ((1 - α₁ - α₂) * Real.log X)
          have hlev1 : V1 = X ^ (α₁ * (σ1 - 1 / 2)) := by
            simpa only [V1, σ1] using two_zpow_eq_rpow_level (X := X) (m := α₁) hXlt hα₁ k.1
          have hlev2 : V2 = X ^ (α₂ * (σ2 - 1 / 2)) := by
            simpa only [V2, σ2] using two_zpow_eq_rpow_level (X := X) (m := α₂) hXlt hα₂ k.2.1
          have hlev3 : V3 = X ^ ((1 - α₁ - α₂) * (σ3 - 1 / 2)) := by
            simpa only [V3, σ3] using two_zpow_eq_rpow_level (X := X) (m := 1 - α₁ - α₂) hXlt hl k.2.2
          have hσ1 : 1 / 2 ≤ σ1 := by
            have hk : (0 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast hk1nn
            have hnum : 0 ≤ (k.1 : ℝ) * Real.log 2 := by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
            have hden : 0 < α₁ * Real.log X := by
              have := Real.log_pos hXlt; positivity
            have h := div_nonneg hnum hden.le
            simp only [σ1]; linarith
          have hσ2 : 1 / 2 ≤ σ2 := by
            have hk : (0 : ℝ) ≤ (k.2.1 : ℝ) := by exact_mod_cast hk2nn
            have hnum : 0 ≤ (k.2.1 : ℝ) * Real.log 2 := by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
            have hden : 0 < α₂ * Real.log X := by
              have := Real.log_pos hXlt; positivity
            have h := div_nonneg hnum hden.le
            simp only [σ2]; linarith
          have hσ3 : 1 / 2 ≤ σ3 := by
            have hk : (0 : ℝ) ≤ (k.2.2 : ℝ) := by exact_mod_cast hk3nn
            have hnum : 0 ≤ (k.2.2 : ℝ) * Real.log 2 := by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
            have hden : 0 < (1 - α₁ - α₂) * Real.log X := by
              have := Real.log_pos hXlt; positivity
            have h := div_nonneg hnum hden.le
            simp only [σ3]; linarith
          let Cell : Finset (ℝ × DirichletCharacter ℂ q) := dyadicCell MAIN f1 f2 f3 k
          have hCellMain : Cell ⊆ MAIN := Finset.filter_subset _ _
          have hCellP : Cell ⊆ P := fun p hp => hMAINsub (hCellMain hp)
          have hCellS : Cell ⊆ S := fun p hp => hPsub (hCellP hp)
          have hspC : WellSpaced Cell := by
            intro p hp p' hp' hne heq
            exact hspace p (hCellS hp) p' (hCellS hp') hne heq
          have htimeC : ∀ p ∈ Cell, |p.1| ≤ T := fun p hp => htimes p (hCellS hp)
          have hposC : ∀ p ∈ Cell, 0 < ‖f1 p‖ ∧ 0 < ‖f2 p‖ ∧ 0 < ‖f3 p‖ := by
            intro p hp
            have h1 : 1 ≤ ‖f1 p‖ := (hbig1 p (hCellMain hp)).1
            have h2 : 1 ≤ ‖f2 p‖ := (hbig2 p (hCellMain hp)).1
            have h3 : 1 ≤ ‖f3 p‖ := (hbig3 p (hCellMain hp)).1
            exact ⟨by linarith, by linarith, by linarith⟩
          have hlow1 : ∀ p ∈ Cell, V1 ≤ ‖f1 p‖ := fun p hp => by
            simpa only [V1] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
              (hposC p hp).2.1 (hposC p hp).2.2).1
          have hlow2 : ∀ p ∈ Cell, V2 ≤ ‖f2 p‖ := fun p hp => by
            simpa only [V2] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
              (hposC p hp).2.1 (hposC p hp).2.2).2.2.1
          have hlow3 : ∀ p ∈ Cell, V3 ≤ ‖f3 p‖ := fun p hp => by
            simpa only [V3] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
              (hposC p hp).2.1 (hposC p hp).2.2).2.2.2.2.1
          by_cases hEmp : Cell = ∅
          · have hzero : (∑ p ∈ dyadicCell MAIN f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) = 0 := by
              rw [show dyadicCell MAIN f1 f2 f3 k = Cell from rfl, hEmp, Finset.sum_empty]
            rw [hzero]
            have h1 : 0 ≤ Cst := hCst0
            have h2 : 0 ≤ Real.log x ^ Dst := Real.rpow_nonneg hlx0.le _
            have h3 : 0 ≤ X ^ (1 / 2 - ε / 72) := Real.rpow_nonneg hX0.le _
            positivity
          obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmp
          have hm1mem : (1 : ℕ) ∈ Sg := Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩
          have hConeq : Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4 = Cf 1 := by
            dsimp only [Cf]; rw [hCfam 1 (by norm_num)]
          have hDoneq : 2 + 3 * Kfam 1 = Df 1 := by
            dsimp only [Df]
          -- the first factor at power one
          have hEa : energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) ≤
              Cefam 1 * Real.log x ^ Kfam 1 := by
            have hbase := hEn 1 (by norm_num) (truncatedCoeffs a c₁ c₂ M ^ 1).coeff
              (truncated_power_bound (c2 := c₂) ha hc₁.le hM0.le 1) x (M ^ 1) hlx
              (by simpa using hM) (by simpa using hMx)
            have hmax1 : (1 : ℝ) ≤ max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) := le_max_left _ _
            have hC0 : 0 ≤ Cem 1 (by norm_num) := (hCempos 1 (by norm_num)).le
            have hlogn : 0 ≤ Real.log x ^ Kem 1 (by norm_num) := Real.rpow_nonneg hlx0.le _
            rw [hCefam 1 (by norm_num), hKfam 1 (by norm_num)]
            calc energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1)
                ≤ Cem 1 (by norm_num) * Real.log x ^ Kem 1 (by norm_num) := hbase
              _ = Cem 1 (by norm_num) * 1 * Real.log x ^ Kem 1 (by norm_num) := by ring
              _ ≤ Cem 1 (by norm_num) * max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) *
                    Real.log x ^ Kem 1 (by norm_num) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax1 hC0) hlogn
              _ = _ := by ring
          have hEa0 : (0 : ℝ) ≤
              energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) :=
            Finset.sum_nonneg (fun n hn => by positivity)
          have hcca' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
              X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := by
            have hcarda := hCpm 1 (by norm_num) x M T V1 q Cell a ha hx hM hMx
              hT hTx hq hqx hV1pos hspC htimeC hlow1
            have hcca : (Cell.card : ℝ) ≤
                (Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) *
                Real.log x ^ (2 + 3 * Kfam 1) *
                X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) :=
              cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := M)
                (V := V1) (Q := Q) (m := α₁) (σ := σ1)
                (e1 := α₁ * (2 - 2 * σ1)) (e2 := 1 - θ + α₁ * Thm4.f σ1) (g := 1)
                (C := Cpm 1 (by norm_num)) (Ce := Cefam 1) (K := Kfam 1)
                (E := energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1))
                hlx hX1 hα₁ rfl hlev1 hQ hM0 hV1pos hV1ge
                (hCpmpos 1 (by norm_num)).le (hCefam0 1 (by norm_num)).le
                (hKfam0 1 (by norm_num)) hEa0
                (by simpa using level_first_term hX0 hα₁ rfl hlev1)
                (by simpa using bracket_one hX0 hX1 hα₁ rfl hlev1 hQ)
                hcarda hEa
            refine card_le_weaken (C := Cpm 1 (by norm_num) *
                (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) (Cg := Cst)
              (D := 2 + 3 * Kfam 1) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hcca
            · have h1 := (hCpmpos 1 (by norm_num)).le
              have h2 := (hCefam0 1 (by norm_num)).le
              positivity
            · rw [hConeq]; exact hCf_le 1 hm1mem
            · rw [hDoneq]; exact hDf_le 1 hm1mem
          -- the second factor at power one
          have hEb : energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) ≤
              Cefam 1 * Real.log x ^ Kfam 1 := by
            have hbase := hEn 1 (by norm_num) (truncatedCoeffs b c₁ c₂ N ^ 1).coeff
              (truncated_power_bound (c2 := c₂) hb hc₁.le hN0.le 1) x (N ^ 1) hlx
              (by simpa using hN) (by simpa using hNx)
            have hmax1 : (1 : ℝ) ≤ max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) := le_max_left _ _
            have hC0 : 0 ≤ Cem 1 (by norm_num) := (hCempos 1 (by norm_num)).le
            have hlogn : 0 ≤ Real.log x ^ Kem 1 (by norm_num) := Real.rpow_nonneg hlx0.le _
            rw [hCefam 1 (by norm_num), hKfam 1 (by norm_num)]
            calc energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1)
                ≤ Cem 1 (by norm_num) * Real.log x ^ Kem 1 (by norm_num) := hbase
              _ = Cem 1 (by norm_num) * 1 * Real.log x ^ Kem 1 (by norm_num) := by ring
              _ ≤ Cem 1 (by norm_num) * max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) *
                    Real.log x ^ Kem 1 (by norm_num) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax1 hC0) hlogn
              _ = _ := by ring
          have hEb0 : (0 : ℝ) ≤
              energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) :=
            Finset.sum_nonneg (fun n hn => by positivity)
          have hccb' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
              X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) := by
            have hcardb := hCpm 1 (by norm_num) x N T V2 q Cell b hb hx hN hNx
              hT hTx hq hqx hV2pos hspC htimeC hlow2
            have hccb : (Cell.card : ℝ) ≤
                (Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) *
                Real.log x ^ (2 + 3 * Kfam 1) *
                X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
              cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := N)
                (V := V2) (Q := Q) (m := α₂) (σ := σ2)
                (e1 := α₂ * (2 - 2 * σ2)) (e2 := 1 - θ + α₂ * Thm4.f σ2) (g := 1)
                (C := Cpm 1 (by norm_num)) (Ce := Cefam 1) (K := Kfam 1)
                (E := energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1))
                hlx hX1 hα₂ rfl hlev2 hQ hN0 hV2pos hV2ge
                (hCpmpos 1 (by norm_num)).le (hCefam0 1 (by norm_num)).le
                (hKfam0 1 (by norm_num)) hEb0
                (by simpa using level_first_term hX0 hα₂ rfl hlev2)
                (by simpa using bracket_one hX0 hX1 hα₂ rfl hlev2 hQ)
                hcardb hEb
            refine card_le_weaken (C := Cpm 1 (by norm_num) *
                (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) (Cg := Cst)
              (D := 2 + 3 * Kfam 1) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hccb
            · have h1 := (hCpmpos 1 (by norm_num)).le
              have h2 := (hCefam0 1 (by norm_num)).le
              positivity
            · rw [hConeq]; exact hCf_le 1 hm1mem
            · rw [hDoneq]; exact hDf_le 1 hm1mem
          -- the third factor at a general power of at most `g0`
          let fam : ℕ → ℝ := fun g => max ((g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
            (1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3))
          have hfam3 : fam 3 = max (3 * (1 - α₁ - α₂) * (2 - 2 * σ3))
              (1 - θ + 3 * (1 - α₁ - α₂) * (4 - 6 * σ3)) := by
            dsimp only [fam]; norm_num
          have hcce : ∀ g, 1 ≤ g → g ≤ g0 →
              (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst * X ^ fam g := by
            intro g hg1 hgg0
            have hCgeq : Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4 = Cf g := by
              dsimp only [Cf]; rw [hCfam g hg1]
            have hDgeq : 2 + 3 * Kfam g = Df g := by
              dsimp only [Df]
            have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
            have hgx : (g : ℝ) ≤ (g0 : ℝ) := by exact_mod_cast hgg0
            have hEe : energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g) ≤
                Cefam g * Real.log x ^ Kfam g := by
              have hambg : 1 ≤ Real.log (x ^ g) := by
                rw [Real.log_pow]
                nlinarith
              have hFL : L ^ g ≤ x ^ g := pow_le_pow_left₀ hL0.le hLx g
              have hbase := hEn g hg1 (truncatedCoeffs e c₁ c₂ L ^ g).coeff
                (truncated_power_bound (c2 := c₂) hecoeff hc₁.le hL0.le g) (x ^ g) (L ^ g) hambg
                (by simpa using hL.trans (le_self_pow₀ hL1 (by omega)))
                (by simpa using hFL)
              rw [hCefam g hg1, hKfam g hg1]
              have hrw : Real.log (x ^ g) ^ Kem g hg1 =
                  (g : ℝ) ^ Kem g hg1 * Real.log x ^ Kem g hg1 := by
                rw [Real.log_pow, Real.mul_rpow (by linarith) hlx0.le]
              rw [hrw] at hbase
              have h1 : (g : ℝ) ^ Kem g hg1 ≤ max 1 ((g0 : ℝ) ^ Kem g hg1) :=
                (Real.rpow_le_rpow (by linarith) hgx (hKem g hg1)).trans (le_max_right _ _)
              have h3 : 0 ≤ Real.log x ^ Kem g hg1 := Real.rpow_nonneg hlx0.le _
              have h4 : 0 ≤ Cem g hg1 := (hCempos g hg1).le
              calc energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g)
                  ≤ Cem g hg1 * ((g : ℝ) ^ Kem g hg1 * Real.log x ^ Kem g hg1) := hbase
                _ ≤ Cem g hg1 * (max 1 ((g0 : ℝ) ^ Kem g hg1) * Real.log x ^ Kem g hg1) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h3) h4
                _ = (Cem g hg1 * max 1 ((g0 : ℝ) ^ Kem g hg1)) * Real.log x ^ Kem g hg1 := by ring
            have hEe0 : (0 : ℝ) ≤
                energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g) :=
              Finset.sum_nonneg (fun n hn => by positivity)
            obtain ⟨hpow1, hpow2, hpow3⟩ := level_pow_terms (X := X) (F := L)
              (V := V3) (l := 1 - α₁ - α₂) (σ := σ3) (g := g) hX0 rfl hlev3
            have hcarde := hCpm g hg1 x L T V3 q Cell e hecoeff hx hL hLx
              hT hTx hq hqx hV3pos hspC htimeC hlow3
            have hccgen : (Cell.card : ℝ) ≤
                (Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4) *
                Real.log x ^ (2 + 3 * Kfam g) *
                X ^ max ((g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
                  (1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3)) :=
              cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := L)
                (V := V3) (Q := Q) (m := 1 - α₁ - α₂) (σ := σ3)
                (e1 := (g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
                (e2 := 1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3)) (g := g)
                (C := Cpm g hg1) (Ce := Cefam g) (K := Kfam g)
                (E := energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g))
                hlx hX1 hl rfl hlev3 hQ hL0 hV3pos hV3ge
                (hCpmpos g hg1).le (hCefam0 g hg1).le (hKfam0 g hg1) hEe0
                (by simpa using hpow1)
                (by simpa using bracket_gen hX0 hX1 hl hg1 rfl hlev3 hQ)
                hcarde hEe
            refine card_le_weaken (C := Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4)
              (Cg := Cst) (D := 2 + 3 * Kfam g) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hccgen
            · have h1 := (hCpmpos g hg1).le
              have h2 := (hCefam0 g hg1).le
              positivity
            · rw [hCgeq]; exact hCf_le g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩)
            · rw [hDgeq]; exact hDf_le g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩)
          let Vals : Finset ℝ := Sg.image fam
          have hValsne : Vals.Nonempty :=
            ⟨fam 1, Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩, rfl⟩⟩
          let s3 : ℝ := Vals.min' hValsne
          have hs3le : ∀ g ∈ Sg, s3 ≤ fam g := fun g hg =>
            Finset.min'_le Vals (fam g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
          have hcce' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst * X ^ s3 := by
            obtain ⟨g1, hg1, hg1eq⟩ := Finset.mem_image.mp (Finset.min'_mem Vals hValsne)
            have h := hcce g1 (Finset.mem_Icc.mp hg1).1 (Finset.mem_Icc.mp hg1).2
            rwa [hg1eq] at h
          have hs1 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
              ≤ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := min_le_left _ _
          have hs2 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
              ≤ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
            (min_le_right _ _).trans (min_le_left _ _)
          have hs3' : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) ≤ s3 :=
            (min_le_right _ _).trans (min_le_right _ _)
          have hs3g : ∀ g ∈ Sg, min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) ≤ fam g :=
            fun g hg => hs3'.trans (hs3le g hg)
          have hcardmin : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
              X ^ min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) :=
            card_le_three_min hlx hCst0 hX1 hcca' hccb' hcce'
          have hcnd : α₂ * Thm4.c σ2 < 1 - θ :=
            nondominant_exponent (X := X) (N := N) (Q := Q) (θ := θ) (n := α₂) (σ := σ2)
              (z := f2 p₀) (k := k.2.1) hXlt hα₂ rfl hQ hσ2 hlev2 (hlow2 p₀ hp₀) hNQ
              (hmemP p₀ (hCellP hp₀)).2.1
          have hnn : α₂ * (2 - 2 * σ2) ≤ 1 - θ + α₂ * Thm4.f σ2 := by
            by_contra hcon
            push_neg at hcon
            exact absurd (Thm4.dominance.mp hcon.le) (not_le.mpr hcnd)
          have hNred : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
              ≤ 1 - θ + α₂ * Thm4.f σ2 := by
            refine hs2.trans ?_
            rw [max_eq_right hnn]
          have hclass : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) +
              (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) + (1 - α₁ - α₂) * (σ3 - 1 / 2)) ≤
              1 / 2 - ε / 72 := by
            have hcndM : α₁ * Thm4.c σ1 < 1 - θ :=
              nondominant_exponent (X := X) (N := M) (Q := Q) (θ := θ) (n := α₁) (σ := σ1)
                (z := f1 p₀) (k := k.1) hXlt hα₁ rfl hQ hσ1 hlev1 (hlow1 p₀ hp₀) hMQ
                (hmemP p₀ (hCellP hp₀)).1
            have hnnM : α₁ * (2 - 2 * σ1) ≤ 1 - θ + α₁ * Thm4.f σ1 := by
              by_contra hcon
              push_neg at hcon
              exact absurd (Thm4.dominance.mp hcon.le) (not_le.mpr hcndM)
            have hMred2 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
                ≤ 1 - θ + α₁ * Thm4.f σ1 := by
              refine hs1.trans ?_
              rw [max_eq_right hnnM]
            have h3 := hs3g 3 (Finset.mem_Icc.mpr ⟨by norm_num, hg0⟩)
            rw [hfam3] at h3
            have hc2 := case2_cell_exponent (m := α₁) (n := α₂) (l := 1 - α₁ - α₂)
              (σ1 := σ1) (σ2 := σ2) (σ3 := σ3)
              (s := min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3))
              hε hα₁.le hα₂.le hml hmsum (by linarith : 1 - α₁ - α₂ < Thm4.gam θ - ε)
              hMred2 hNred h3
            linarith
          have hlevels : 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
              8 * X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) + (1 - α₁ - α₂) * (σ3 - 1 / 2)) := by
            have hmul : (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
                X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
                  (1 - α₁ - α₂) * (σ3 - 1 / 2)) :=
              cell_level_mul hX0 (by simpa only [V1] using hlev1)
                (by simpa only [V2] using hlev2) (by simpa only [V3] using hlev3)
            calc 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
                8 * ((2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) := by ring
              _ = 8 * X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
                    (1 - α₁ - α₂) * (σ3 - 1 / 2)) := by rw [hmul]
          exact cell_sum_combine MAIN f1 f2 f3 k hX0 hX1 hε hCst0 hlx
            (fun p hp => ⟨lt_of_lt_of_le zero_lt_one (hbig1 p hp).1,
              lt_of_lt_of_le zero_lt_one (hbig2 p hp).1,
              lt_of_lt_of_le zero_lt_one (hbig3 p hp).1⟩)
            hcardmin hlevels hclass
        have hsum := sum_over_cells (q := q) (S := MAIN) (f1 := f1) (f2 := f2) (f3 := f3)
          (x := x) (V := max Cn 1 * x ^ 2)
          (H := 8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72)) (Clev := Clev)
          hlx (by positivity) hClev0 (by positivity) hbig1 hbig2 hbig3 hcell hClev'
        have h3r : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := Real.rpow_natCast _ _
        have hlog3 : Real.log x ^ (3 + Dst) = Real.log x ^ 3 * Real.log x ^ Dst := by
          rw [Real.rpow_add hlx0 (3 : ℝ) Dst, h3r]
        have hsave2 : X ^ (1 / 2 - ε / 72) * Real.log x ^ (3 + Dst) ≤
            R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
          power_saving_with_log (x := x) (X := X) (A := A) (δ := ε / 72) (k := 3 + Dst)
            (by linarith) hXge hA (by linarith) (by linarith)
        calc (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖)
            ≤ (Clev * Real.log x) ^ 3 *
                (8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72)) := hsum
          _ = 8 * Cst * Clev ^ 3 * (Real.log x ^ 3 * Real.log x ^ Dst) *
                X ^ (1 / 2 - ε / 72) := by ring
          _ = 8 * Cst * Clev ^ 3 * Real.log x ^ (3 + Dst) * X ^ (1 / 2 - ε / 72) := by rw [← hlog3]
          _ = 8 * Cst * Clev ^ 3 * (X ^ (1 / 2 - ε / 72) * Real.log x ^ (3 + Dst)) := by ring
          _ ≤ 8 * Cst * Clev ^ 3 * (R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
              mul_le_mul_of_nonneg_left hsave2 (by positivity)
          _ = 8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
      rw [← hsplit]
      calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) + (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖)
          ≤ 4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
            8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
          add_le_add htinyA hMAINA
        _ = (4 * H * R1 + 8 * Cst * Clev ^ 3 * R2) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
    exact hgoal
  
  
  
  
  
  
  
  /- LEAF. Page 14, Case 3 i, display 3.14.
  The third factor has norm at most its length to one quarter.
  CONDITIONAL on the original three inputs. -/
  have first_small_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ thirdNormPart (casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
        (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
        (X ^ (1 - α₁ - α₂)) true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    intro B
    refine ⟨1, by norm_num, ?_⟩
    intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
    obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
    obtain ⟨Ce, K0, hCe, hK0, he⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
    obtain ⟨Cd, Dd, hCd, hDd, hd⟩ := dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
    let D0 := max Dd (K0 + 1)
    have hD0 : 0 ≤ D0 := hDd.trans (le_max_left _ _)
    let H := Cd + 2 * Cm * Ce
    let R := ((ε / 4) / (A + D0)) ^ (-(A + D0))
    have hH : 0 < H := by dsimp [H]; positivity
    have hR : 0 ≤ R := by dsimp [R]; positivity
    refine ⟨H * R, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
    let M := X ^ α₁
    let N := X ^ α₂
    let L := X ^ (1 - α₁ - α₂)
    let Q : ℝ := (q : ℝ) * T
    let P := thirdNormPart (casePart S
      (fun p => dominanceFlag Q M (dirPoly a c₁ c₂ M p.2 (half p.1)))
      (fun p => dominanceFlag Q N (dirPoly b c₁ c₂ N p.2 (half p.1))) true false)
      (fun p => dirPoly e c₁ c₂ L p.2 (half p.1)) L true
    have hsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hx3 : 3 ≤ x := by linarith
    have hlx : 1 ≤ Real.log x := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
      linarith [Real.log_three_gt_d9]
    have hlx0 : 0 < Real.log x := by linarith
    have hXge : x ≤ X := by
      rcases hX with rfl | rfl
      · exact le_rfl
      · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
        calc
          x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
    have hX0 : 0 < X := by linarith
    have hX1 : 1 ≤ X := by linarith
    have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
    have hlog0 : 0 ≤ Real.log x ^ D0 := Real.rpow_nonneg hlx0.le _
    by_cases hEmpty : P = ∅
    · change (∑ p ∈ P, _) ≤ _
      rw [hEmpty, Finset.sum_empty]
      positivity
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hcase := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) hcase.2
    have hsp : WellSpaced P := by
      intro p hp p' hp' hne heq
      exact hspace p (hsub hp) p' (hsub hp') hne heq
    have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
    have hHc : Cd ≤ H := by
      dsimp [H]
      have hh : 0 ≤ 2 * Cm * Ce := by positivity
      linarith
    have hHm : 2 * Cm * Ce ≤ H := by dsimp [H]; linarith
    have hlogd : Real.log x ^ Dd ≤ Real.log x ^ D0 :=
      Real.rpow_le_rpow_of_exponent_le hlx (le_max_left _ _)
    have hlogk : Real.log x ^ (K0 + 1) ≤ Real.log x ^ D0 :=
      Real.rpow_le_rpow_of_exponent_le hlx (le_max_right _ _)
    have hmomentM : (∑ p ∈ P, ‖dirPoly a c₁ c₂ M p.2 (half p.1)‖ ^ 2) ≤
        H * M * Real.log x ^ D0 := by
      have hh := hd x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
        (by intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1)
      exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hHc (by dsimp [M]; positivity))
        hlogd (by positivity) (by dsimp [M]; positivity))
    have hmomentN : (∑ p ∈ P, ‖dirPoly b c₁ c₂ N p.2 (half p.1)‖ ^ 2) ≤
        H * Q * Real.log x ^ D0 := by
      have hmF := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
      have heF := he b hb x N hlx hN hNx
      have hEnonneg : 0 ≤ energy b c₁ c₂ N := Finset.sum_nonneg (fun n hn => by positivity)
      calc
        _ ≤ Cm * Real.log x * (Q + N) * energy b c₁ c₂ N := hmF
        _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by gcongr <;> linarith
        _ = (2 * Cm * Ce) * Q * (Real.log x ^ K0 * Real.log x) := by ring
        _ = (2 * Cm * Ce) * Q * Real.log x ^ (K0 + 1) := by rw [Real.rpow_add hlx0, Real.rpow_one]
        _ ≤ H * Q * Real.log x ^ D0 := mul_le_mul
          (mul_le_mul_of_nonneg_right hHm hQ0) hlogk (by positivity) (by positivity)
    have hpair' := pair_of_square_bounds P
      (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
      (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hH.le
      (by dsimp [M]; positivity) hQ0 (Real.rpow_nonneg hlx0.le D0) hmomentM hmomentN
    have htriple := triple_of_pair_bound P
      (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
      (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
      (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
      (by dsimp [L]; positivity : 0 ≤ L ^ (1 / 4 : ℝ)) hpair'
      (by intro p hp; exact of_decide_eq_true (Finset.mem_filter.mp hp).2)
    have hpow : Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 - ε / 4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, show Q = X ^ (1 - θ) from hqT]
      dsimp [M, L]
      rw [← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le,
        ← Real.rpow_add hX0, ← Real.rpow_add hX0]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      have hab' := (abs_lt.mp hab).2
      linarith
    have hsave := power_saving_with_log (by linarith : 1 < x) hXge hA
      (by linarith : 0 < ε / 4) hD0
    calc
      _ ≤ (H * Real.sqrt M * Real.sqrt Q * Real.log x ^ D0) * L ^ (1 / 4 : ℝ) := htriple
      _ = H * (Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ)) * Real.log x ^ D0 := by ring
      _ ≤ H * X ^ (1 / 2 - ε / 4) * Real.log x ^ D0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le) hlog0
      _ = H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ D0) := by ring
      _ ≤ H * (R * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_left hsave hH.le
      _ = _ := by ring
  
  /- LEAF. Page 14, Case 3 ii, displays 3.15 and 3.16.
  Only the part above the third norm threshold remains. The bounded choice
  of polynomial power and its level-set summation remain OPEN.
  Retain the existing proved repair for the g equal to one branch.
  CONDITIONAL on the original three inputs. -/
  have first_large_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ thirdNormPart (casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
        (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
        (X ^ (1 - α₁ - α₂)) false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    intro B
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro ε hε hεu' c₁ c₂ hc₁ hc₂ Kfun A hA
    have hεu : ε ≤ 1 / 2 := le_of_lt hεu'
    -- ## constants, all named before `θ`
    obtain ⟨Cn, hCn, hnorm⟩ := dirPoly_norm_uniform B c₁ c₂ hc₁ (hc₁.trans hc₂)
    have hCn1 : 0 < max Cn 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    obtain ⟨g0', hg0'1, hcut'⟩ := exists_uniform_power_cutoff hε
    let g0 : ℕ := max g0' 3
    have hg0 : 3 ≤ g0 := le_max_right _ _
    have hg01 : 1 ≤ g0 := le_trans hg0'1 (le_max_left _ _)
    have hlevel_pkg : ∀ g : ℕ, 1 ≤ g → ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
        ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
        CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        0 < V → WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖dirPoly a c₁ c₂ F p.2 (half p.1)‖) →
        (let E := energy (truncatedCoeffs a c₁ c₂ F ^ g).coeff (c₁ ^ g) (c₂ ^ g) (F ^ g);
          (S.card : ℝ) ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) *
            (F ^ g / V ^ (2 * g) +
              (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)))) := by
      intro g hg
      exact power_level_min hmean hlarge B c₁ c₂ hc₁ hc₂ g hg
    choose Cpm hCpmpos hCpm using hlevel_pkg
    have henergy_pkg : ∀ g : ℕ, 1 ≤ g → ∃ Ce K : ℝ, 0 < Ce ∧ 0 ≤ K ∧
        ∀ f : ℕ → ℂ, CoeffBound f ((g : ℝ) * (max B 0 + 1)) → ∀ x F : ℝ,
          1 ≤ Real.log x → 2 ≤ F → F ≤ x →
          energy f (c₁ ^ g) (c₂ ^ g) F ≤ Ce * Real.log x ^ K := by
      intro g hg
      exact energy_log_uniform henergy ((g : ℝ) * (max B 0 + 1)) (c₁ ^ g) (c₂ ^ g)
        (pow_pos hc₁ g) (pow_lt_pow_left₀ hc₂ hc₁.le (by omega))
    choose Cem Kem hCempos hKem hEn using henergy_pkg
    obtain ⟨Cd, Dd, hCd, hDd, hd⟩ :=
      dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
    obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
    obtain ⟨Ce, K0, hCe, hK0, hen⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
    let Cfam : ℕ → ℝ := fun g => if h : 1 ≤ g then Cpm g h else 1
    let Cefam : ℕ → ℝ := fun g => if h : 1 ≤ g then Cem g h * max 1 ((g0 : ℝ) ^ Kem g h) else 1
    let Kfam : ℕ → ℝ := fun g => if h : 1 ≤ g then Kem g h else 0
    have hCfam : ∀ g (hg : 1 ≤ g), Cfam g = Cpm g hg := fun g hg => by
      dsimp [Cfam]; rw [dif_pos hg]
    have hCefam : ∀ g (hg : 1 ≤ g),
        Cefam g = Cem g hg * max 1 ((g0 : ℝ) ^ Kem g hg) := fun g hg => by
      dsimp [Cefam]; rw [dif_pos hg]
    have hKfam : ∀ g (hg : 1 ≤ g), Kfam g = Kem g hg := fun g hg => by
      dsimp [Kfam]; rw [dif_pos hg]
    have hCfam0 : ∀ g, 1 ≤ g → 0 < Cfam g := fun g hg => by
      rw [hCfam g hg]; exact hCpmpos g hg
    have hCefam0 : ∀ g, 1 ≤ g → 0 < Cefam g := fun g hg => by
      rw [hCefam g hg]
      exact mul_pos (hCempos g hg) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hKfam0 : ∀ g, 1 ≤ g → 0 ≤ Kfam g := fun g hg => by
      rw [hKfam g hg]; exact hKem g hg
    let Cf : ℕ → ℝ := fun g => Cfam g * (Cefam g + 16 * Cefam g ^ 3) * 4
    let Df : ℕ → ℝ := fun g => 2 + 3 * Kfam g
    have hCf0 : ∀ g, 1 ≤ g → 0 ≤ Cf g := fun g hg => by
      have h1 := (hCfam0 g hg).le
      have h2 : 0 ≤ Cefam g + 16 * Cefam g ^ 3 := by
        have := (hCefam0 g hg).le; positivity
      dsimp [Cf]; positivity
    have hDf0 : ∀ g, 1 ≤ g → 0 ≤ Df g := fun g hg => by
      have := hKfam0 g hg; dsimp [Df]; linarith
    let Sg : Finset ℕ := Finset.Icc 1 g0
    have hSgne : Sg.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩⟩
    let Cst : ℝ := ∑ g ∈ Sg, Cf g
    let Dsum : ℝ := ∑ g ∈ Sg, Df g
    let Dst : ℝ := Dsum + Dd + (K0 + 1) + 2
    have hCst0 : 0 ≤ Cst :=
      Finset.sum_nonneg (fun g hg => hCf0 g (Finset.mem_Icc.mp hg).1)
    have hDsum0 : 0 ≤ Dsum :=
      Finset.sum_nonneg (fun g hg => hDf0 g (Finset.mem_Icc.mp hg).1)
    have hDst0 : 0 ≤ Dst := by dsimp [Dst]; linarith
    have hCf_le : ∀ g ∈ Sg, Cf g ≤ Cst := fun g hg =>
      Finset.single_le_sum (fun i hi => hCf0 i (Finset.mem_Icc.mp hi).1) hg
    have hDf_le : ∀ g ∈ Sg, Df g ≤ Dst := fun g hg => by
      have h1 : Df g ≤ Dsum :=
        Finset.single_le_sum (fun i hi => hDf0 i (Finset.mem_Icc.mp hi).1) hg
      have h2 : 0 ≤ Dd := hDd
      have h3 : 0 ≤ K0 + 1 := by linarith
      dsimp [Dst]; linarith
    have hDd_le : Dd ≤ Dst := by dsimp [Dst]; linarith
    have hK0_le : K0 + 1 ≤ Dst := by dsimp [Dst]; linarith [hDd]
    have h2_le : (2 : ℝ) ≤ Dst := by dsimp [Dst]; linarith [hDd, hK0]
    let Clev : ℝ := (Real.log (max Cn 1) + 2) / Real.log 2 + 2
    let H : ℝ := Cd + 2 * Cm * Ce + Cn + 1
    have hCmCe : 2 * Cm * Ce ≤ H := by dsimp [H]; nlinarith [hCd, hCn]
    have hHd : Cd ≤ H := by dsimp [H]; nlinarith [hCm, hCe, hCn]
    have hHn : Cn ≤ H := by dsimp [H]; nlinarith [hCd, hCm, hCe]
    have hH0 : 0 < H := lt_of_lt_of_le hCd hHd
    have hClev0 : 0 ≤ Clev := by
      have h1 : 0 ≤ Real.log (max Cn 1) := Real.log_nonneg (le_max_right _ _)
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      dsimp [Clev]; positivity
    let R1 : ℝ := ((ε / 4) / (A + Dst)) ^ (-(A + Dst))
    let R2 : ℝ := ((ε / 72) / (A + (3 + Dst))) ^ (-(A + (3 + Dst)))
    have hR10 : 0 ≤ R1 := Real.rpow_nonneg (by positivity) _
    have hR20 : 0 ≤ R2 := Real.rpow_nonneg (by positivity) _
    refine ⟨4 * H * R1 + 8 * Cst * Clev ^ 3 * R2, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
    let M : ℝ := X ^ α₁
    let N : ℝ := X ^ α₂
    let L : ℝ := X ^ (1 - α₁ - α₂)
    let Q : ℝ := (q : ℝ) * T
    let f1 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly a c₁ c₂ M p.2 (half p.1)
    let f2 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly b c₁ c₂ N p.2 (half p.1)
    let f3 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly e c₁ c₂ L p.2 (half p.1)
    let P : Finset (ℝ × DirichletCharacter ℂ q) := thirdNormPart (casePart S
      (fun p => dominanceFlag Q M (f1 p))
      (fun p => dominanceFlag Q N (f2 p)) true false) f3 L false
    have hx3 : 3 ≤ x := by linarith
    have hlx : 1 ≤ Real.log x := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
      linarith [Real.log_three_gt_d9]
    have hlx0 : 0 < Real.log x := by linarith
    have hXge : x ≤ X := by
      rcases hX with rfl | rfl
      · exact le_rfl
      · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
        calc
          x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
    have hX0 : 0 < X := by linarith
    have hX1 : 1 ≤ X := by linarith
    have hXlt : 1 < X := by linarith
    have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
    have hQ : Q = X ^ (1 - θ) := hqT
    have hθ5 : θ ≤ 3 / 5 := by linarith
    have hcut : θ - ε / 2 < Thm4.d θ g0 :=
      (hcut' θ (by linarith) (by linarith)).trans_le
        (Thm4.d_mono (by linarith) (Nat.cast_nonneg _) (by exact_mod_cast le_max_left g0' 3))
    have hα₁ : 0 < α₁ := by
      rcases le_or_gt α₁ 0 with h | h
      · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
      · exact h
    have hα₂ : 0 < α₂ := by
      rcases le_or_gt α₂ 0 with h | h
      · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
      · exact h
    have hl : 0 < 1 - α₁ - α₂ := by
      rcases le_or_gt (1 - α₁ - α₂) 0 with h | h
      · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
      · exact h
    have hml : 0 ≤ 1 - α₁ - α₂ := hl.le
    have hM0 : 0 < M := by dsimp [M]; positivity
    have hN0 : 0 < N := by dsimp [N]; positivity
    have hL0 : 0 < L := by dsimp [L]; positivity
    have hL1 : 1 ≤ L := by linarith
    have hmsum : α₁ + α₂ + (1 - α₁ - α₂) = 1 := by ring
    have hLQ : L ≤ Q := by
      rw [hQ]
      dsimp [L]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      have hg1 := Thm4.gam_le_one θ
      nlinarith
    have hmemP : ∀ p ∈ P, dominanceFlag Q M (f1 p) = true ∧
        dominanceFlag Q N (f2 p) = false ∧ L ^ (1 / 4 : ℝ) < ‖f3 p‖ := by
      intro p hp
      have h1 := (Finset.mem_filter.mp hp).1
      exact ⟨(Finset.mem_filter.mp h1).2.1, (Finset.mem_filter.mp h1).2.2,
        not_le.mp (of_decide_eq_false (Finset.mem_filter.mp hp).2)⟩
    have hPsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hsp : WellSpaced P := by
      intro p hp p' hp' hne heq
      exact hspace p (hPsub hp) p' (hPsub hp') hne heq
    have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hPsub hp)
    have hf3big : ∀ p ∈ P, 1 ≤ ‖f3 p‖ := by
      intro p hp
      have h := (hmemP p hp).2.2
      have h1 : (1 : ℝ) ≤ L ^ (1 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith
    have hgoal : (∑ p ∈ P, ‖f1 p * f2 p * f3 p‖) ≤
        (4 * H * R1 + 8 * Cst * Clev ^ 3 * R2) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
      by_cases hEmpty : P = ∅
      · rw [hEmpty, Finset.sum_empty]; positivity
      obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) (hmemP p₀ hp₀).2.1
      have hlogD : ∀ {d : ℝ}, d ≤ Dst → Real.log x ^ d ≤ Real.log x ^ Dst :=
        fun hd' => Real.rpow_le_rpow_of_exponent_le hlx hd'
      have hmomentM : (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ H * X ^ α₁ * Real.log x ^ Dst := by
        have hh := hd x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
          (fun p hp => (hmemP p hp).1)
        have h1 : Real.log x ^ Dd ≤ Real.log x ^ Dst := hlogD hDd_le
        have h2 : Cd * M ≤ H * M := mul_le_mul_of_nonneg_right hHd hM0.le
        calc (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ Cd * M * Real.log x ^ Dd := hh
          _ ≤ H * M * Real.log x ^ Dst :=
              mul_le_mul h2 h1 (Real.rpow_nonneg hlx0.le _) (by positivity)
          _ = H * X ^ α₁ * Real.log x ^ Dst := by rw [show M = X ^ α₁ from rfl]
      have hmomentN : (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
        have hh := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
        have hQN : Q + N ≤ 2 * Q := by linarith
        have heN : energy b c₁ c₂ N ≤ Ce * Real.log x ^ K0 := hen b hb x N hlx hN hNx
        have hEnn : 0 ≤ energy b c₁ c₂ N := Finset.sum_nonneg (fun n hn => by positivity)
        have hstep : Cm * Real.log x * (Q + N) * energy b c₁ c₂ N ≤
            Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
          have h1 : 0 ≤ Cm * Real.log x := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hQN h1) heN hEnn (by positivity)
        have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
          rw [Real.rpow_add hlx0, Real.rpow_one]
        have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
            H * Q * Real.log x ^ Dst := by
          have h1 : 2 * Cm * Ce ≤ H := hCmCe
          have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0_le
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
            (Real.rpow_nonneg hlx0.le _) (by positivity)
        calc (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ Cm * Real.log x * (Q + N) * energy b c₁ c₂ N := hh
          _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
          _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
          _ ≤ H * Q * Real.log x ^ Dst := hfin
          _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
      have hmomentE : (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
        have hh := hm x L T q P e hecoeff hx hL hLx hT hTx hq hqx hsp htime
        have hQL : Q + L ≤ 2 * Q := by linarith
        have heL : energy e c₁ c₂ L ≤ Ce * Real.log x ^ K0 := hen e hecoeff x L hlx hL hLx
        have hEnn : 0 ≤ energy e c₁ c₂ L := Finset.sum_nonneg (fun n hn => by positivity)
        have hstep : Cm * Real.log x * (Q + L) * energy e c₁ c₂ L ≤
            Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
          have h1 : 0 ≤ Cm * Real.log x := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hQL h1) heL hEnn (by positivity)
        have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
          rw [Real.rpow_add hlx0, Real.rpow_one]
        have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
            H * Q * Real.log x ^ Dst := by
          have h1 : 2 * Cm * Ce ≤ H := hCmCe
          have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0_le
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
            (Real.rpow_nonneg hlx0.le _) (by positivity)
        calc (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ Cm * Real.log x * (Q + L) * energy e c₁ c₂ L := hh
          _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
          _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
          _ ≤ H * Q * Real.log x ^ Dst := hfin
          _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
      -- ## the large-value part over the dyadic cells
      let TIN : Finset (ℝ × DirichletCharacter ℂ q) := P.filter (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1)
      let MAIN : Finset (ℝ × DirichletCharacter ℂ q) :=
        P.filter (fun p => ¬ (‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1))
      have hTINsub : TIN ⊆ P := Finset.filter_subset _ _
      have hMAINsub : MAIN ⊆ P := Finset.filter_subset _ _
      have hsplit : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) +
          (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖) = ∑ p ∈ P, ‖f1 p * f2 p * f3 p‖ :=
        Finset.sum_filter_add_sum_filter_not P (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1) _
      have hexptiny : max α₁ (1 - θ) + (1 - θ) ≤ 1 - ε / 2 := by
        have hα : α₁ < θ - ε / 2 := by
          have h1 := (abs_lt.mp hab).2
          have h2 : α₁ + α₂ < 1 := by linarith
          linarith
        rcases le_or_gt α₁ (1 - θ) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h.le]; linarith
      have htinyA : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ≤
          4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
        have hbase := tiny_final (q := q) (P := P) (TIN := TIN) (f1 := f1) (f2 := f2) (f3 := f3)
          (x := x) (X := X) (ε := ε) (D := Dst) (HB := H) (a := α₁) (b := 1 - θ) (e := 1 - θ)
          hlx hX1 hH0.le hDst0 hε hTINsub (fun p hp => (Finset.mem_filter.mp hp).2)
          hmomentM hmomentN hmomentE hexptiny
        have hsave1 : X ^ (1 / 2 - ε / 4) * Real.log x ^ Dst ≤
            R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
          power_saving_with_log (x := x) (X := X) (A := A) (δ := ε / 4) (k := Dst)
            (by linarith) hXge hA (by linarith) hDst0
        calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖)
            ≤ 4 * H * Real.log x ^ Dst * X ^ (1 / 2 - ε / 4) := hbase
          _ = 4 * H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ Dst) := by ring
          _ ≤ 4 * H * (R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
              mul_le_mul_of_nonneg_left hsave1 (by positivity)
          _ = 4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
      have hMAINA : (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖) ≤
          8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
        have hV1 : 1 ≤ max Cn 1 * x ^ 2 := by
          have h1 : 1 ≤ max Cn 1 := le_max_right _ _
          have h2 : 1 ≤ x ^ 2 := one_le_pow₀ (by linarith)
          exact one_le_mul_of_one_le_of_one_le h1 h2
        have hbig1 : ∀ p ∈ MAIN, 1 ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ max Cn 1 * x ^ 2 := by
          intro p hp
          have hntiny := (Finset.mem_filter.mp hp).2
          push_neg at hntiny
          refine ⟨le_of_lt hntiny.1, ?_⟩
          have hb1 := hnorm a ha M (by linarith : 1 ≤ M) q p.2 p.1
          have hMx2 : M ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hM0.le hMx 2
          calc ‖f1 p‖ ≤ Cn * M ^ 2 := hb1
            _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hMx2 hCn.le
            _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hbig2 : ∀ p ∈ MAIN, 1 ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ max Cn 1 * x ^ 2 := by
          intro p hp
          have hntiny := (Finset.mem_filter.mp hp).2
          push_neg at hntiny
          refine ⟨le_of_lt hntiny.2, ?_⟩
          have hb2 := hnorm b hb N (by linarith : 1 ≤ N) q p.2 p.1
          have hNx2 : N ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hN0.le hNx 2
          calc ‖f2 p‖ ≤ Cn * N ^ 2 := hb2
            _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hNx2 hCn.le
            _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hbig3 : ∀ p ∈ MAIN, 1 ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ max Cn 1 * x ^ 2 := by
          intro p hp
          refine ⟨hf3big p (hMAINsub hp), ?_⟩
          have hb3 := hnorm e hecoeff L (by linarith : 1 ≤ L) q p.2 p.1
          have hLx2 : L ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hL0.le hLx 2
          calc ‖f3 p‖ ≤ Cn * L ^ 2 := hb3
            _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hLx2 hCn.le
            _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hClev' : ((dyadicLevels 1 (max Cn 1 * x ^ 2)).card : ℝ) ≤ Clev * Real.log x :=
          quadratic_level_count (le_max_right _ _) (by linarith) hlx
        have hzp : ∀ j : ℤ, 0 ≤ j → (1 : ℝ) ≤ (2 : ℝ) ^ j := by
          intro j hj
          rw [← zpow_zero (2 : ℝ)]
          exact zpow_le_zpow_right₀ (by norm_num) hj
        -- the energy of a fixed power at the enlarged ambient point
        have hamb : ∀ (g : ℕ) (hg : 1 ≤ g) (F : ℝ), 2 ≤ F → F ≤ x →
            1 ≤ Real.log (x ^ g) := by
          intro g hg F hF hFx
          rw [Real.log_pow]
          have h1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
          nlinarith
        have hcell : ∀ k ∈ dyadicLevels 1 (max Cn 1 * x ^ 2) ×ˢ dyadicLevels 1 (max Cn 1 * x ^ 2) ×ˢ
            dyadicLevels 1 (max Cn 1 * x ^ 2),
            (∑ p ∈ dyadicCell MAIN f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤
              8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72) := by
          intro k hk
          obtain ⟨hk1, hk23⟩ := Finset.mem_product.mp hk
          obtain ⟨hk2, hk3⟩ := Finset.mem_product.mp hk23
          have hk1nn : (0 : ℤ) ≤ k.1 := by
            have h := (Finset.mem_Icc.mp hk1).1
            rwa [Int.log_one_right] at h
          have hk2nn : (0 : ℤ) ≤ k.2.1 := by
            have h := (Finset.mem_Icc.mp hk2).1
            rwa [Int.log_one_right] at h
          have hk3nn : (0 : ℤ) ≤ k.2.2 := by
            have h := (Finset.mem_Icc.mp hk3).1
            rwa [Int.log_one_right] at h
          let V1 : ℝ := (2 : ℝ) ^ k.1
          let V2 : ℝ := (2 : ℝ) ^ k.2.1
          let V3 : ℝ := (2 : ℝ) ^ k.2.2
          have hV1ge : (1 : ℝ) ≤ V1 := by simpa only [V1] using hzp k.1 hk1nn
          have hV2ge : (1 : ℝ) ≤ V2 := by simpa only [V2] using hzp k.2.1 hk2nn
          have hV3ge : (1 : ℝ) ≤ V3 := by simpa only [V3] using hzp k.2.2 hk3nn
          have hV1pos : 0 < V1 := lt_of_lt_of_le zero_lt_one hV1ge
          have hV2pos : 0 < V2 := lt_of_lt_of_le zero_lt_one hV2ge
          have hV3pos : 0 < V3 := lt_of_lt_of_le zero_lt_one hV3ge
          let σ1 : ℝ := 1 / 2 + (k.1 : ℝ) * Real.log 2 / (α₁ * Real.log X)
          let σ2 : ℝ := 1 / 2 + (k.2.1 : ℝ) * Real.log 2 / (α₂ * Real.log X)
          let σ3 : ℝ := 1 / 2 + (k.2.2 : ℝ) * Real.log 2 / ((1 - α₁ - α₂) * Real.log X)
          have hlev1 : V1 = X ^ (α₁ * (σ1 - 1 / 2)) := by
            simpa only [V1, σ1] using two_zpow_eq_rpow_level (X := X) (m := α₁) hXlt hα₁ k.1
          have hlev2 : V2 = X ^ (α₂ * (σ2 - 1 / 2)) := by
            simpa only [V2, σ2] using two_zpow_eq_rpow_level (X := X) (m := α₂) hXlt hα₂ k.2.1
          have hlev3 : V3 = X ^ ((1 - α₁ - α₂) * (σ3 - 1 / 2)) := by
            simpa only [V3, σ3] using two_zpow_eq_rpow_level (X := X) (m := 1 - α₁ - α₂) hXlt hl k.2.2
          have hσ1 : 1 / 2 ≤ σ1 := by
            have hk : (0 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast hk1nn
            have hnum : 0 ≤ (k.1 : ℝ) * Real.log 2 := by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
            have hden : 0 < α₁ * Real.log X := by
              have := Real.log_pos hXlt; positivity
            have h := div_nonneg hnum hden.le
            simp only [σ1]; linarith
          have hσ2 : 1 / 2 ≤ σ2 := by
            have hk : (0 : ℝ) ≤ (k.2.1 : ℝ) := by exact_mod_cast hk2nn
            have hnum : 0 ≤ (k.2.1 : ℝ) * Real.log 2 := by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
            have hden : 0 < α₂ * Real.log X := by
              have := Real.log_pos hXlt; positivity
            have h := div_nonneg hnum hden.le
            simp only [σ2]; linarith
          have hσ3 : 1 / 2 ≤ σ3 := by
            have hk : (0 : ℝ) ≤ (k.2.2 : ℝ) := by exact_mod_cast hk3nn
            have hnum : 0 ≤ (k.2.2 : ℝ) * Real.log 2 := by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
            have hden : 0 < (1 - α₁ - α₂) * Real.log X := by
              have := Real.log_pos hXlt; positivity
            have h := div_nonneg hnum hden.le
            simp only [σ3]; linarith
          let Cell : Finset (ℝ × DirichletCharacter ℂ q) := dyadicCell MAIN f1 f2 f3 k
          have hCellMain : Cell ⊆ MAIN := Finset.filter_subset _ _
          have hCellP : Cell ⊆ P := fun p hp => hMAINsub (hCellMain hp)
          have hCellS : Cell ⊆ S := fun p hp => hPsub (hCellP hp)
          have hspC : WellSpaced Cell := by
            intro p hp p' hp' hne heq
            exact hspace p (hCellS hp) p' (hCellS hp') hne heq
          have htimeC : ∀ p ∈ Cell, |p.1| ≤ T := fun p hp => htimes p (hCellS hp)
          have hposC : ∀ p ∈ Cell, 0 < ‖f1 p‖ ∧ 0 < ‖f2 p‖ ∧ 0 < ‖f3 p‖ := by
            intro p hp
            have h1 : 1 ≤ ‖f1 p‖ := (hbig1 p (hCellMain hp)).1
            have h2 : 1 ≤ ‖f2 p‖ := (hbig2 p (hCellMain hp)).1
            have h3 : 1 ≤ ‖f3 p‖ := (hbig3 p (hCellMain hp)).1
            exact ⟨by linarith, by linarith, by linarith⟩
          have hlow1 : ∀ p ∈ Cell, V1 ≤ ‖f1 p‖ := fun p hp => by
            simpa only [V1] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
              (hposC p hp).2.1 (hposC p hp).2.2).1
          have hlow2 : ∀ p ∈ Cell, V2 ≤ ‖f2 p‖ := fun p hp => by
            simpa only [V2] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
              (hposC p hp).2.1 (hposC p hp).2.2).2.2.1
          have hlow3 : ∀ p ∈ Cell, V3 ≤ ‖f3 p‖ := fun p hp => by
            simpa only [V3] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
              (hposC p hp).2.1 (hposC p hp).2.2).2.2.2.2.1
          by_cases hEmp : Cell = ∅
          · have hzero : (∑ p ∈ dyadicCell MAIN f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) = 0 := by
              rw [show dyadicCell MAIN f1 f2 f3 k = Cell from rfl, hEmp, Finset.sum_empty]
            rw [hzero]
            have h1 : 0 ≤ Cst := hCst0
            have h2 : 0 ≤ Real.log x ^ Dst := Real.rpow_nonneg hlx0.le _
            have h3 : 0 ≤ X ^ (1 / 2 - ε / 72) := Real.rpow_nonneg hX0.le _
            positivity
          obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmp
          have hm1mem : (1 : ℕ) ∈ Sg := Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩
          have hConeq : Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4 = Cf 1 := by
            dsimp only [Cf]; rw [hCfam 1 (by norm_num)]
          have hDoneq : 2 + 3 * Kfam 1 = Df 1 := by
            dsimp only [Df]
          -- the first factor at power one
          have hEa : energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) ≤
              Cefam 1 * Real.log x ^ Kfam 1 := by
            have hbase := hEn 1 (by norm_num) (truncatedCoeffs a c₁ c₂ M ^ 1).coeff
              (truncated_power_bound (c2 := c₂) ha hc₁.le hM0.le 1) x (M ^ 1) hlx
              (by simpa using hM) (by simpa using hMx)
            have hmax1 : (1 : ℝ) ≤ max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) := le_max_left _ _
            have hC0 : 0 ≤ Cem 1 (by norm_num) := (hCempos 1 (by norm_num)).le
            have hlogn : 0 ≤ Real.log x ^ Kem 1 (by norm_num) := Real.rpow_nonneg hlx0.le _
            rw [hCefam 1 (by norm_num), hKfam 1 (by norm_num)]
            calc energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1)
                ≤ Cem 1 (by norm_num) * Real.log x ^ Kem 1 (by norm_num) := hbase
              _ = Cem 1 (by norm_num) * 1 * Real.log x ^ Kem 1 (by norm_num) := by ring
              _ ≤ Cem 1 (by norm_num) * max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) *
                    Real.log x ^ Kem 1 (by norm_num) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax1 hC0) hlogn
              _ = _ := by ring
          have hEa0 : (0 : ℝ) ≤
              energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) :=
            Finset.sum_nonneg (fun n hn => by positivity)
          have hcca' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
              X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := by
            have hcarda := hCpm 1 (by norm_num) x M T V1 q Cell a ha hx hM hMx
              hT hTx hq hqx hV1pos hspC htimeC hlow1
            have hcca : (Cell.card : ℝ) ≤
                (Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) *
                Real.log x ^ (2 + 3 * Kfam 1) *
                X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) :=
              cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := M)
                (V := V1) (Q := Q) (m := α₁) (σ := σ1)
                (e1 := α₁ * (2 - 2 * σ1)) (e2 := 1 - θ + α₁ * Thm4.f σ1) (g := 1)
                (C := Cpm 1 (by norm_num)) (Ce := Cefam 1) (K := Kfam 1)
                (E := energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1))
                hlx hX1 hα₁ rfl hlev1 hQ hM0 hV1pos hV1ge
                (hCpmpos 1 (by norm_num)).le (hCefam0 1 (by norm_num)).le
                (hKfam0 1 (by norm_num)) hEa0
                (by simpa using level_first_term hX0 hα₁ rfl hlev1)
                (by simpa using bracket_one hX0 hX1 hα₁ rfl hlev1 hQ)
                hcarda hEa
            refine card_le_weaken (C := Cpm 1 (by norm_num) *
                (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) (Cg := Cst)
              (D := 2 + 3 * Kfam 1) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hcca
            · have h1 := (hCpmpos 1 (by norm_num)).le
              have h2 := (hCefam0 1 (by norm_num)).le
              positivity
            · rw [hConeq]; exact hCf_le 1 hm1mem
            · rw [hDoneq]; exact hDf_le 1 hm1mem
          -- the second factor at power one
          have hEb : energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) ≤
              Cefam 1 * Real.log x ^ Kfam 1 := by
            have hbase := hEn 1 (by norm_num) (truncatedCoeffs b c₁ c₂ N ^ 1).coeff
              (truncated_power_bound (c2 := c₂) hb hc₁.le hN0.le 1) x (N ^ 1) hlx
              (by simpa using hN) (by simpa using hNx)
            have hmax1 : (1 : ℝ) ≤ max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) := le_max_left _ _
            have hC0 : 0 ≤ Cem 1 (by norm_num) := (hCempos 1 (by norm_num)).le
            have hlogn : 0 ≤ Real.log x ^ Kem 1 (by norm_num) := Real.rpow_nonneg hlx0.le _
            rw [hCefam 1 (by norm_num), hKfam 1 (by norm_num)]
            calc energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1)
                ≤ Cem 1 (by norm_num) * Real.log x ^ Kem 1 (by norm_num) := hbase
              _ = Cem 1 (by norm_num) * 1 * Real.log x ^ Kem 1 (by norm_num) := by ring
              _ ≤ Cem 1 (by norm_num) * max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) *
                    Real.log x ^ Kem 1 (by norm_num) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax1 hC0) hlogn
              _ = _ := by ring
          have hEb0 : (0 : ℝ) ≤
              energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) :=
            Finset.sum_nonneg (fun n hn => by positivity)
          have hccb' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
              X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) := by
            have hcardb := hCpm 1 (by norm_num) x N T V2 q Cell b hb hx hN hNx
              hT hTx hq hqx hV2pos hspC htimeC hlow2
            have hccb : (Cell.card : ℝ) ≤
                (Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) *
                Real.log x ^ (2 + 3 * Kfam 1) *
                X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
              cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := N)
                (V := V2) (Q := Q) (m := α₂) (σ := σ2)
                (e1 := α₂ * (2 - 2 * σ2)) (e2 := 1 - θ + α₂ * Thm4.f σ2) (g := 1)
                (C := Cpm 1 (by norm_num)) (Ce := Cefam 1) (K := Kfam 1)
                (E := energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1))
                hlx hX1 hα₂ rfl hlev2 hQ hN0 hV2pos hV2ge
                (hCpmpos 1 (by norm_num)).le (hCefam0 1 (by norm_num)).le
                (hKfam0 1 (by norm_num)) hEb0
                (by simpa using level_first_term hX0 hα₂ rfl hlev2)
                (by simpa using bracket_one hX0 hX1 hα₂ rfl hlev2 hQ)
                hcardb hEb
            refine card_le_weaken (C := Cpm 1 (by norm_num) *
                (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) (Cg := Cst)
              (D := 2 + 3 * Kfam 1) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hccb
            · have h1 := (hCpmpos 1 (by norm_num)).le
              have h2 := (hCefam0 1 (by norm_num)).le
              positivity
            · rw [hConeq]; exact hCf_le 1 hm1mem
            · rw [hDoneq]; exact hDf_le 1 hm1mem
          -- the third factor at a general power of at most `g0`
          let fam : ℕ → ℝ := fun g => max ((g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
            (1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3))
          have hfam3 : fam 3 = max (3 * (1 - α₁ - α₂) * (2 - 2 * σ3))
              (1 - θ + 3 * (1 - α₁ - α₂) * (4 - 6 * σ3)) := by
            dsimp only [fam]; norm_num
          have hcce : ∀ g, 1 ≤ g → g ≤ g0 →
              (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst * X ^ fam g := by
            intro g hg1 hgg0
            have hCgeq : Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4 = Cf g := by
              dsimp only [Cf]; rw [hCfam g hg1]
            have hDgeq : 2 + 3 * Kfam g = Df g := by
              dsimp only [Df]
            have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
            have hgx : (g : ℝ) ≤ (g0 : ℝ) := by exact_mod_cast hgg0
            have hEe : energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g) ≤
                Cefam g * Real.log x ^ Kfam g := by
              have hambg : 1 ≤ Real.log (x ^ g) := by
                rw [Real.log_pow]
                nlinarith
              have hFL : L ^ g ≤ x ^ g := pow_le_pow_left₀ hL0.le hLx g
              have hbase := hEn g hg1 (truncatedCoeffs e c₁ c₂ L ^ g).coeff
                (truncated_power_bound (c2 := c₂) hecoeff hc₁.le hL0.le g) (x ^ g) (L ^ g) hambg
                (by simpa using hL.trans (le_self_pow₀ hL1 (by omega)))
                (by simpa using hFL)
              rw [hCefam g hg1, hKfam g hg1]
              have hrw : Real.log (x ^ g) ^ Kem g hg1 =
                  (g : ℝ) ^ Kem g hg1 * Real.log x ^ Kem g hg1 := by
                rw [Real.log_pow, Real.mul_rpow (by linarith) hlx0.le]
              rw [hrw] at hbase
              have h1 : (g : ℝ) ^ Kem g hg1 ≤ max 1 ((g0 : ℝ) ^ Kem g hg1) :=
                (Real.rpow_le_rpow (by linarith) hgx (hKem g hg1)).trans (le_max_right _ _)
              have h3 : 0 ≤ Real.log x ^ Kem g hg1 := Real.rpow_nonneg hlx0.le _
              have h4 : 0 ≤ Cem g hg1 := (hCempos g hg1).le
              calc energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g)
                  ≤ Cem g hg1 * ((g : ℝ) ^ Kem g hg1 * Real.log x ^ Kem g hg1) := hbase
                _ ≤ Cem g hg1 * (max 1 ((g0 : ℝ) ^ Kem g hg1) * Real.log x ^ Kem g hg1) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h3) h4
                _ = (Cem g hg1 * max 1 ((g0 : ℝ) ^ Kem g hg1)) * Real.log x ^ Kem g hg1 := by ring
            have hEe0 : (0 : ℝ) ≤
                energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g) :=
              Finset.sum_nonneg (fun n hn => by positivity)
            obtain ⟨hpow1, hpow2, hpow3⟩ := level_pow_terms (X := X) (F := L)
              (V := V3) (l := 1 - α₁ - α₂) (σ := σ3) (g := g) hX0 rfl hlev3
            have hcarde := hCpm g hg1 x L T V3 q Cell e hecoeff hx hL hLx
              hT hTx hq hqx hV3pos hspC htimeC hlow3
            have hccgen : (Cell.card : ℝ) ≤
                (Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4) *
                Real.log x ^ (2 + 3 * Kfam g) *
                X ^ max ((g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
                  (1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3)) :=
              cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := L)
                (V := V3) (Q := Q) (m := 1 - α₁ - α₂) (σ := σ3)
                (e1 := (g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
                (e2 := 1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3)) (g := g)
                (C := Cpm g hg1) (Ce := Cefam g) (K := Kfam g)
                (E := energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g))
                hlx hX1 hl rfl hlev3 hQ hL0 hV3pos hV3ge
                (hCpmpos g hg1).le (hCefam0 g hg1).le (hKfam0 g hg1) hEe0
                (by simpa using hpow1)
                (by simpa using bracket_gen hX0 hX1 hl hg1 rfl hlev3 hQ)
                hcarde hEe
            refine card_le_weaken (C := Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4)
              (Cg := Cst) (D := 2 + 3 * Kfam g) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hccgen
            · have h1 := (hCpmpos g hg1).le
              have h2 := (hCefam0 g hg1).le
              positivity
            · rw [hCgeq]; exact hCf_le g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩)
            · rw [hDgeq]; exact hDf_le g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩)
          let Vals : Finset ℝ := Sg.image fam
          have hValsne : Vals.Nonempty :=
            ⟨fam 1, Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩, rfl⟩⟩
          let s3 : ℝ := Vals.min' hValsne
          have hs3le : ∀ g ∈ Sg, s3 ≤ fam g := fun g hg =>
            Finset.min'_le Vals (fam g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
          have hcce' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst * X ^ s3 := by
            obtain ⟨g1, hg1, hg1eq⟩ := Finset.mem_image.mp (Finset.min'_mem Vals hValsne)
            have h := hcce g1 (Finset.mem_Icc.mp hg1).1 (Finset.mem_Icc.mp hg1).2
            rwa [hg1eq] at h
          have hs1 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
              ≤ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := min_le_left _ _
          have hs2 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
              ≤ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
            (min_le_right _ _).trans (min_le_left _ _)
          have hs3' : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) ≤ s3 :=
            (min_le_right _ _).trans (min_le_right _ _)
          have hs3g : ∀ g ∈ Sg, min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) ≤ fam g :=
            fun g hg => hs3'.trans (hs3le g hg)
          have hcardmin : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
              X ^ min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) :=
            card_le_three_min hlx hCst0 hX1 hcca' hccb' hcce'
          have hcnd : α₂ * Thm4.c σ2 < 1 - θ :=
            nondominant_exponent (X := X) (N := N) (Q := Q) (θ := θ) (n := α₂) (σ := σ2)
              (z := f2 p₀) (k := k.2.1) hXlt hα₂ rfl hQ hσ2 hlev2 (hlow2 p₀ hp₀) hNQ
              (hmemP p₀ (hCellP hp₀)).2.1
          have hnn : α₂ * (2 - 2 * σ2) ≤ 1 - θ + α₂ * Thm4.f σ2 := by
            by_contra hcon
            push_neg at hcon
            exact absurd (Thm4.dominance.mp hcon.le) (not_le.mpr hcnd)
          have hNred : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
              ≤ 1 - θ + α₂ * Thm4.f σ2 := by
            refine hs2.trans ?_
            rw [max_eq_right hnn]
          have hclass : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) +
              (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) + (1 - α₁ - α₂) * (σ3 - 1 / 2)) ≤
              1 / 2 - ε / 72 := by
            by_cases hdM : 1 - θ ≤ α₁ * Thm4.c σ1
            · have hdom : 1 - θ + α₁ * Thm4.f σ1 ≤ α₁ * (2 - 2 * σ1) := Thm4.dominance.mpr hdM
              have hMred : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                  (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
                  ≤ α₁ * (2 - 2 * σ1) := by
                refine hs1.trans ?_
                rw [max_eq_left hdom]
              have hcl := mixed_cell_exponent (m := α₁) (n := α₂) (σ1 := σ1) (σ2 := σ2)
                (σ3 := σ3)
                (s := min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                  (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)) (g0 := g0)
                hε hεu hθu hα₂.le hml hab hgam hcut hcnd hMred hNred
                (fun g hg1 hgg0 => hs3g g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩))
              linarith
            · have hMred2 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                  (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
                  ≤ 1 - θ + α₁ * Thm4.f σ1 := by
                refine hs1.trans ?_
                rw [max_eq_right ?_]
                by_contra hcon
                push_neg at hcon
                exact hdM (Thm4.dominance.mp hcon.le)
              have h3 := hs3g 3 (Finset.mem_Icc.mpr ⟨by norm_num, hg0⟩)
              rw [hfam3] at h3
              have hc2 := case2_cell_exponent (m := α₁) (n := α₂) (l := 1 - α₁ - α₂)
                (σ1 := σ1) (σ2 := σ2) (σ3 := σ3)
                (s := min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                  (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3))
                hε hα₁.le hα₂.le hml hmsum (by linarith : 1 - α₁ - α₂ < Thm4.gam θ - ε)
                hMred2 hNred h3
              linarith
          have hlevels : 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
              8 * X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) + (1 - α₁ - α₂) * (σ3 - 1 / 2)) := by
            have hmul : (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
                X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
                  (1 - α₁ - α₂) * (σ3 - 1 / 2)) :=
              cell_level_mul hX0 (by simpa only [V1] using hlev1)
                (by simpa only [V2] using hlev2) (by simpa only [V3] using hlev3)
            calc 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
                8 * ((2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) := by ring
              _ = 8 * X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
                    (1 - α₁ - α₂) * (σ3 - 1 / 2)) := by rw [hmul]
          exact cell_sum_combine MAIN f1 f2 f3 k hX0 hX1 hε hCst0 hlx
            (fun p hp => ⟨lt_of_lt_of_le zero_lt_one (hbig1 p hp).1,
              lt_of_lt_of_le zero_lt_one (hbig2 p hp).1,
              lt_of_lt_of_le zero_lt_one (hbig3 p hp).1⟩)
            hcardmin hlevels hclass
        have hsum := sum_over_cells (q := q) (S := MAIN) (f1 := f1) (f2 := f2) (f3 := f3)
          (x := x) (V := max Cn 1 * x ^ 2)
          (H := 8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72)) (Clev := Clev)
          hlx (by positivity) hClev0 (by positivity) hbig1 hbig2 hbig3 hcell hClev'
        have h3r : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := Real.rpow_natCast _ _
        have hlog3 : Real.log x ^ (3 + Dst) = Real.log x ^ 3 * Real.log x ^ Dst := by
          rw [Real.rpow_add hlx0 (3 : ℝ) Dst, h3r]
        have hsave2 : X ^ (1 / 2 - ε / 72) * Real.log x ^ (3 + Dst) ≤
            R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
          power_saving_with_log (x := x) (X := X) (A := A) (δ := ε / 72) (k := 3 + Dst)
            (by linarith) hXge hA (by linarith) (by linarith)
        calc (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖)
            ≤ (Clev * Real.log x) ^ 3 *
                (8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72)) := hsum
          _ = 8 * Cst * Clev ^ 3 * (Real.log x ^ 3 * Real.log x ^ Dst) *
                X ^ (1 / 2 - ε / 72) := by ring
          _ = 8 * Cst * Clev ^ 3 * Real.log x ^ (3 + Dst) * X ^ (1 / 2 - ε / 72) := by rw [← hlog3]
          _ = 8 * Cst * Clev ^ 3 * (X ^ (1 / 2 - ε / 72) * Real.log x ^ (3 + Dst)) := by ring
          _ ≤ 8 * Cst * Clev ^ 3 * (R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
              mul_le_mul_of_nonneg_left hsave2 (by positivity)
          _ = 8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
      rw [← hsplit]
      calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) + (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖)
          ≤ 4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
            8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
          add_le_add htinyA hMAINA
        _ = (4 * H * R1 + 8 * Cst * Clev ^ 3 * R2) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
    exact hgoal
  
  
  
  
  
  
  
  
  /- LEAF. Page 13, Case 1, displays 3.11 and 3.12, followed by 3.2.
  Dyadically sum only the part where both first terms dominate.
  This uses the logarithmic energy bound, not a positive power substitute.
  OPEN. CONDITIONAL on the three explicit analytic inputs. -/
  have both_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    intro B
    refine ⟨1, by norm_num, ?_⟩
    intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C, D, hC, hD, hm⟩ := dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
    let A' := A + D
    have hA' : 0 < A' := by dsimp [A']; linarith
    refine ⟨C * |K A'|, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    let M := X ^ α₁
    let N := X ^ α₂
    let L := X ^ (1 - α₁ - α₂)
    let P := casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) M (dirPoly a c₁ c₂ M p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) N (dirPoly b c₁ c₂ N p.2 (half p.1))) true true
    have hsub : P ⊆ S := Finset.filter_subset _ _
    have hsp : WellSpaced P := by
      intro p hp p' hp' hne heq
      exact hspace p (hsub hp) p' (hsub hp') hne heq
    have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
    have hma := hm x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
      (by intro p hp; exact (Finset.mem_filter.mp hp).2.1)
    have hmb := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
      (by intro p hp; exact (Finset.mem_filter.mp hp).2.2)
    have hMN := pair_of_square_bounds P
      (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
      (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hC.le
      (by dsimp [M]; positivity) (by dsimp [N]; positivity)
      (Real.rpow_nonneg (Real.log_nonneg (by linarith)) D) hma hmb
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hL0 : 0 ≤ L := by dsimp [L]; linarith
    have hthird : ∀ p ∈ P, ‖dirPoly e c₁ c₂ L p.2 (half p.1)‖ ≤
        |K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
      intro p hp
      exact (hsmall A' hA' p (hsub hp)).trans (by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have htriple := triple_of_pair_bound P
      (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
      (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
      (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
      (by positivity : 0 ≤ |K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) hMN hthird
    have hXpos : 0 < X := by
      rcases hX with rfl | rfl
      · linarith
      · positivity
    have hsqrt : Real.sqrt M * Real.sqrt N * L ^ (1 / 2 : ℝ) = X ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      dsimp [M, N, L]
      rw [← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le,
        ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
      congr 1
      ring
    have hlog : Real.log x ^ D * Real.log x ^ (-A') = Real.log x ^ (-A) := by
      rw [← Real.rpow_add (Real.log_pos (by linarith : 1 < x))]
      congr 1
      dsimp [A']
      ring
    calc
      _ ≤ (C * Real.sqrt M * Real.sqrt N * Real.log x ^ D) *
          (|K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) := htriple
      _ = C * |K A'| * (Real.sqrt M * Real.sqrt N * L ^ (1 / 2 : ℝ)) *
          (Real.log x ^ D * Real.log x ^ (-A')) := by ring
      _ = _ := by rw [hsqrt, hlog]
  
  
  
  /- LEAF. Page 13, Case 2 i and ii, displays 3.10 to 3.13.
  Dyadically sum only the part where neither first term dominates.
  The three branches of gamma provide the power savings.
  OPEN. CONDITIONAL on the three explicit analytic inputs. -/
  have neither_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    intro B
    obtain ⟨η0, hη0, h0⟩ := neither_small_third hmean hlarge henergy B
    obtain ⟨η1, hη1, h1⟩ := neither_large_third hmean hlarge henergy B
    refine ⟨min η0 η1, lt_min hη0 hη1, ?_⟩
    intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C0, hc0⟩ := h0 ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C1, hc1⟩ := h1 ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) c₁ c₂ hc₁ hc₂ K A hA
    refine ⟨C0 + C1, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hs0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hs1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    rw [sum_third_parts _ (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂))]
    exact (add_le_add hs0 hs1).trans_eq (by ring)
  
  
  
  /- LEAF. Page 14, Case 3 i and ii, displays 3.14 to 3.16.
  Dyadically sum only the part where the first polynomial dominates.
  Use the repaired g equal to one branch already proved in DecompC165c.
  The bounded power selection and the remaining summation are retained here.
  OPEN. CONDITIONAL on the three explicit analytic inputs. -/
  have first_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    intro B
    obtain ⟨η0, hη0, h0⟩ := first_small_third hmean hlarge henergy B
    obtain ⟨η1, hη1, h1⟩ := first_large_third hmean hlarge henergy B
    refine ⟨min η0 η1, lt_min hη0 hη1, ?_⟩
    intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C0, hc0⟩ := h0 ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C1, hc1⟩ := h1 ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) c₁ c₂ hc₁ hc₂ K A hA
    refine ⟨C0 + C1, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hs0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hs1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    rw [sum_third_parts _ (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂))]
    exact (add_le_add hs0 hs1).trans_eq (by ring)
  
  
  /- Page 15, Case 4 follows from Case 3 by interchanging M and N.
  CONDITIONAL on first_dominant and its three explicit analytic inputs. -/
  have second_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
      (henergy : EnergyLogBound) :
      ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a b e : ℕ → ℂ,
      1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
      2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
      1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
      2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
      2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
      WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      CoeffBound a B → CoeffBound b B → CoeffBound e B →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
          K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
      ∑ p ∈ casePart S
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
        (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
        dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    intro B
    obtain ⟨η, hη, hcase⟩ := first_dominant hmean hlarge henergy B
    refine ⟨η, hη, ?_⟩
    intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C, hC⟩ := hcase ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
    refine ⟨C, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have h := hC θ α₂ α₁ x X T q S b a e hθ hθu
      (by simpa only [abs_sub_comm] using hab) (by convert hgam using 1 <;> ring)
      hx hX hq hqx hT hTx hqT hN hNx hM hMx
      (by convert hL using 1 <;> congr 1 <;> ring)
      (by convert hLx using 1 <;> congr 1 <;> ring)
      hspace htimes hb ha he (by convert hsmall using 1 <;> congr 1 <;> ring)
    convert h using 1
    · rw [casePart_swap]
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      congr 1
      · ring
      · congr 2
        ring
  
  /- Pages 12 to 15, exact original dyadic_mean_value statement assembled
  from the four smaller dominance parts. No direct sorry.
  CONDITIONAL on the three OPEN cases and the original analytic inputs. -/
  have finish : Thm4.Theorem4Paper := by
    intro B
    obtain ⟨η0, hη0, h0⟩ := both_dominant hmean hlarge henergy B
    obtain ⟨η1, hη1, h1⟩ := neither_dominant hmean hlarge henergy B
    obtain ⟨η2, hη2, h2⟩ := first_dominant hmean hlarge henergy B
    obtain ⟨η3, hη3, h3⟩ := second_dominant hmean hlarge henergy B
    refine ⟨min η0 (min η1 (min η2 η3)), by positivity, ?_⟩
    intro ε hε hεη
    have he0 : ε < η0 := lt_of_lt_of_le hεη (min_le_left _ _)
    have he1 : ε < η1 := lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_left _ _))
    have he2 : ε < η2 := lt_of_lt_of_le hεη
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have he3 : ε < η3 := lt_of_lt_of_le hεη
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    intro c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C0, hc0⟩ := h0 ε hε he0 c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C1, hc1⟩ := h1 ε hε he1 c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C2, hc2⟩ := h2 ε hε he2 c₁ c₂ hc₁ hc₂ K A hA
    obtain ⟨C3, hc3⟩ := h3 ε hε he3 c₁ c₂ hc₁ hc₂ K A hA
    refine ⟨C0 + C1 + C2 + C3, ?_⟩
    intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
      hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hb0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hb1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hb2 := hc2 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    have hb3 := hc3 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
    rw [sum_four_parts S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1)))]
    calc
      _ ≤ C0 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
          C1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
          C2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
          C3 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        add_le_add (add_le_add (add_le_add hb0 hb1) hb2) hb3
      _ = _ := by ring
  
  exact finish

/-- P0069 pages 11 to 15. The exact Section 3 assembly.
CONDITIONAL ON the two cited Lemma 1 leaves. The energy input is proved. -/
theorem section3_mean_values : Thm4.Theorem4Paper := by
  exact dyadic_mean_value hybrid_mean_square hybrid_large_values energy_log_bound

end LeanLab.BHP1997.DecompC165c
