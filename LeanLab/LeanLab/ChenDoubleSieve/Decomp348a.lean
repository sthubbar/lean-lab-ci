import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Section3
import LeanLab.BS2022GRH.PortedMertens

/-!
Supply split for the lower sieve bounds in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, pages 6, 38 and 39.
The finite level retains the logarithmic loss from Lemma 2.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The filter of sufficiently large even natural numbers. -/
def evenAtTop : Filter ℕ := atTop ⊓ principal {N | Even N}

/-- The local Euler product V at the fixed lower sifting level. -/
def lowerDensity (N : ℕ) : ℝ :=
  ∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))

/-- The normalized Euler product used in equations 10.2 and 10.5. -/
def scaledDensity (N : ℕ) : ℝ := log N * lowerDensity N / CN N

/-- The residual logarithmic level after fixing a divisor d. -/
def lowerLevel (B : ℝ) (N d : ℕ) : ℝ :=
  log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / d) /
    log ((N : ℝ) ^ kappa1)

/-- The finite level main term before the normalization in equation 10.2. -/
def main0 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / log N * lowerDensity N * f (lowerLevel B N 1)

/-- The finite logarithmic loss has this exact form at divisor one. -/
theorem lowerLevel_one (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    lowerLevel B N 1 = 6 - 12 * B * (log (log N) / log N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold lowerLevel
  simp only [Nat.cast_one, div_one]
  rw [log_div (rpow_pos_of_pos hpos _).ne' (rpow_pos_of_pos hlog _).ne',
    log_rpow hpos, log_rpow hlog, log_rpow hpos]
  norm_num [kappa1]
  field_simp
  <;> ring

/-- The residual level at divisor one tends to six for each fixed loss B. -/
theorem lowerLevel_one_tendsto (B : ℝ) :
    Tendsto (fun N : ℕ => lowerLevel B N 1) atTop (𝓝 6) := by
  have hsmall : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun N : ℕ => 6 - 12 * B * (log (log N) / log N))
      atTop (𝓝 6) := by
    simpa using (tendsto_const_nhds (x := (6 : ℝ))).sub
      ((hsmall.comp hlog).const_mul (12 * B))
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (lowerLevel_one B hN).symm

/-- Divide the finite main term by the exact normalizer. -/
theorem main0_ratio (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    main0 f B N / Θ N = scaledDensity N * f (lowerLevel B N 1) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold main0 scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']

/-- `N.primesLE` is the set of primes below `N + 1`. -/
private lemma primesLE_eq_filter_range (N : ℕ) :
    N.primesLE = (range (N + 1)).filter Nat.Prime := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨hN, hp⟩; exact ⟨⟨by have := hp.two_le; omega, by omega⟩, hp⟩

/-- The two-sided bound `|log (1 - t) + t| ≤ 2 t²` for `0 ≤ t ≤ 1/2`. -/
private lemma log_one_sub_add_abs_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    |Real.log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have ht1 : 0 < 1 - t := by linarith
  have hinv : 0 < (1 - t)⁻¹ := by positivity
  have hle : Real.log (1 - t) + t ≤ 0 := by
    have h := Real.one_sub_inv_le_log_of_pos hinv
    rw [Real.log_inv] at h
    simp only [inv_inv] at h
    linarith
  have hge : -(2 * t ^ 2) ≤ Real.log (1 - t) + t := by
    have h := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_inv] at h
    have h2 : (1 - t)⁻¹ - 1 = t / (1 - t) := by
      field_simp
      ring
    rw [h2] at h
    have h5 : t * t / (1 - t) ≤ 2 * t ^ 2 := by
      rw [div_le_iff₀ ht1]
      nlinarith
    have h6 : t - t / (1 - t) = -(t * t / (1 - t)) := by
      field_simp [ht1.ne']
      ring
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- The summed error `log (1 - 1/p) + 1/p` is summable over the primes. -/
private lemma summable_log_one_sub_inv :
    Summable (fun n : ℕ => if n.Prime then Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ) else 0) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => 2 / (n : ℝ) ^ 2) ?_ ?_
  · have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    simpa only [mul_one_div] using h.mul_left 2
  · intro n
    by_cases hn : n.Prime
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
      rw [ite_eq_left hn, Real.norm_eq_abs]
      have ht := log_one_sub_add_abs_le (1 / (n : ℝ)) (by positivity)
        (by
          have hp : (0 : ℝ) < n := by linarith
          rw [div_le_iff₀ hp]
          linarith)
      have he : (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) ^ 2 := by
        rw [div_pow, one_pow]
      rw [he] at ht
      calc |Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)| ≤ 2 * (1 / (n : ℝ) ^ 2) := ht
        _ = 2 / (n : ℝ) ^ 2 := by ring
    · rw [ite_eq_right hn, norm_zero]
      positivity

/-- The partial sums of the error over `N.primesLE` converge to the total. -/
private lemma tendsto_sum_log_one_sub_inv :
    Tendsto (fun N : ℕ => ∑ p ∈ N.primesLE,
        (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) atTop
      (𝓝 (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))) := by
  have hts : (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
      = ∑' (b : ℕ), if b.Prime then Real.log (1 - 1 / (b : ℝ)) + 1 / (b : ℝ) else 0 :=
    LeanLab.BS2022GRH.PortedMertens.Mertens.tsum_primes_eq_tsum_ite
      (fun n : ℕ => Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))
  rw [hts]
  have h := (summable_log_one_sub_inv.hasSum).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine h.congr' (Filter.Eventually.of_forall fun N => ?_)
  simp only [Function.comp_apply]
  rw [← Finset.sum_filter, ← primesLE_eq_filter_range]


/-- Mertens' third theorem, product form, along the naturals. -/
private lemma tendsto_prod_primesLE_mul_log :
    Tendsto (fun N : ℕ => (∏ p ∈ N.primesLE, (1 - 1 / (p : ℝ))) * Real.log N)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  set T : ℝ := ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) with hT
  have hu : Tendsto (fun N : ℕ => (∑ p ∈ N.primesLE, 1 / (p : ℝ)) - Real.log (Real.log N))
      atTop (𝓝 (Real.eulerMascheroniConstant + T)) := by
    have h := LeanLab.BS2022GRH.PortedMertens.solution.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Nat.floor_natCast, hT] using h
  have hS : Tendsto (fun N : ℕ => ∑ p ∈ N.primesLE,
      (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) atTop (𝓝 T) := by
    simpa only [hT] using tendsto_sum_log_one_sub_inv
  have hdiff : Tendsto (fun N : ℕ =>
      (∑ p ∈ N.primesLE, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
      - ((∑ p ∈ N.primesLE, 1 / (p : ℝ)) - Real.log (Real.log N))) atTop
      (𝓝 (T - (Real.eulerMascheroniConstant + T))) := hS.sub hu
  have hlim : Tendsto (fun N : ℕ =>
      (∑ p ∈ N.primesLE, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
      - ((∑ p ∈ N.primesLE, 1 / (p : ℝ)) - Real.log (Real.log N))) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    have he : T - (Real.eulerMascheroniConstant + T) = -Real.eulerMascheroniConstant := by ring
    rwa [he] at hdiff
  have harg : Tendsto (fun N : ℕ =>
      (∑ p ∈ N.primesLE, Real.log (1 - 1 / (p : ℝ))) + Real.log (Real.log N))
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    refine hlim.congr' (Filter.Eventually.of_forall fun N => ?_)
    rw [Finset.sum_add_distrib]
    ring
  have hexp : Tendsto (fun N : ℕ =>
      Real.exp ((∑ p ∈ N.primesLE, Real.log (1 - 1 / (p : ℝ))) + Real.log (Real.log N)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) :=
    (Real.continuous_exp.tendsto _).comp harg
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hprod : (∏ p ∈ N.primesLE, (1 - 1 / (p : ℝ)))
      = Real.exp (∑ p ∈ N.primesLE, Real.log (1 - 1 / (p : ℝ))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hp1 : 0 < 1 - 1 / (p : ℝ) := by
      have hle : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    exact (Real.exp_log hp1).symm
  rw [hprod, Real.exp_add, Real.exp_log hlogpos]

/-- Splitting the prime below `N` off the primes up to `N`. -/
private lemma primesLE_split (N : ℕ) :
    N.primesLE = if N.Prime then insert N ((range N).filter Nat.Prime)
      else (range N).filter Nat.Prime := by
  by_cases hN : N.Prime
  · rw [if_pos hN]
    ext p
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hle, hp⟩
      by_cases h : p = N
      · exact Or.inl h
      · exact Or.inr ⟨by omega, hp⟩
    · rintro (rfl | ⟨hlt, hp⟩)
      · exact ⟨le_rfl, hN⟩
      · exact ⟨by omega, hp⟩
  · rw [if_neg hN]
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hle, hp⟩
      have hne : p ≠ N := fun h => hN (h ▸ hp)
      exact ⟨by omega, hp⟩
    · rintro ⟨hlt, hp⟩
      exact ⟨by omega, hp⟩

/-- The product over `N.primesLE` against the product over primes below `N`. -/
private lemma prod_primesLE_eq (N : ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ N.primesLE, f p)
      = (∏ p ∈ (range N).filter Nat.Prime, f p) * (if N.Prime then f N else 1) := by
  rw [primesLE_split]
  by_cases hN : N.Prime
  · rw [if_pos hN, if_pos hN, Finset.prod_insert]
    · ring
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
  · rw [if_neg hN, if_neg hN, mul_one]

/-- The boundary factor `1 - 1/N` (or one) tends to one. -/
private lemma tendsto_boundary_factor :
    Tendsto (fun N : ℕ => if N.Prime then 1 - 1 / (N : ℝ) else 1) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hle : ∀ N : ℕ, ‖(if N.Prime then 1 - 1 / (N : ℝ) else 1) - 1‖ ≤ 1 / (N : ℝ) := by
    intro N
    by_cases hN : N.Prime
    · rw [if_pos hN]
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have := hN.two_le
        exact_mod_cast (show 0 < N by omega)
      have hrew : 1 - 1 / (N : ℝ) - 1 = -(1 / (N : ℝ)) := by ring
      rw [hrew, norm_neg, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hNpos)]
    · rw [if_neg hN, sub_self, norm_zero]
      exact div_nonneg zero_le_one (Nat.cast_nonneg N)
  exact squeeze_zero (fun N => norm_nonneg _) hle hb

/-- The boundary factor is never zero. -/
private lemma boundary_factor_ne_zero (N : ℕ) (hN : 2 ≤ N) :
    (if N.Prime then 1 - 1 / (N : ℝ) else 1) ≠ 0 := by
  by_cases h : N.Prime
  · rw [if_pos h]
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast h.two_le
    have : 1 / (N : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    intro hc
    linarith
  · rw [if_neg h]
    norm_num

/-- Mertens' third theorem with the strict cutoff over `range N`. -/
private lemma tendsto_prod_range_mul_log :
    Tendsto (fun N : ℕ => (∏ p ∈ (range N).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log N)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hA := tendsto_prod_primesLE_mul_log
  have hc := tendsto_boundary_factor
  have hdiv := hA.div hc (by norm_num : (1 : ℝ) ≠ 0)
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hsplit := prod_primesLE_eq N (fun p : ℕ => 1 - 1 / (p : ℝ))
  have hne := boundary_factor_ne_zero N hN
  dsimp only [Pi.div_apply]
  rw [hsplit, div_eq_iff hne]
  ring


/-- `log ⌈z⌉₊ - log z` tends to zero. -/
private lemma tendsto_log_ceil_sub_log :
    Tendsto (fun z : ℝ => Real.log ⌈z⌉₊ - Real.log z) atTop (𝓝 0) := by
  have hb : Tendsto (fun z : ℝ => 1 / z) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    have h1 : (0 : ℝ) < z := by linarith
    have h2 : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
    have h3 : (0 : ℝ) < (⌈z⌉₊ : ℝ) := by linarith
    linarith [Real.log_le_log h1 h2]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    have h1 : (0 : ℝ) < z := by linarith
    have h2 : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one (by linarith)
    have h3 : (0 : ℝ) < z + 1 := by linarith
    have h2' : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
    have h3' : (0 : ℝ) < (⌈z⌉₊ : ℝ) := by linarith
    have h4 : Real.log (⌈z⌉₊ : ℝ) ≤ Real.log (z + 1) := Real.log_le_log h3' (le_of_lt h2)
    have h5 : Real.log (z + 1) - Real.log z = Real.log ((z + 1) / z) := by
      rw [Real.log_div (by linarith) (ne_of_gt h1)]
    have h6 : Real.log ((z + 1) / z) ≤ (z + 1) / z - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h7 : (z + 1) / z - 1 = 1 / z := by
      field_simp
      ring
    linarith

/-- `log z / log ⌈z⌉₊` tends to one. -/
private lemma tendsto_log_div_log_ceil :
    Tendsto (fun z : ℝ => Real.log z / Real.log ⌈z⌉₊) atTop (𝓝 1) := by
  have hd := tendsto_log_ceil_sub_log
  have hceil : Tendsto (fun z : ℝ => (⌈z⌉₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_ceil_atTop
  have hinv : Tendsto (fun z : ℝ => (Real.log ⌈z⌉₊)⁻¹) atTop (𝓝 0) :=
    (tendsto_log_atTop.comp hceil).inv_tendsto_atTop
  have hprod := hd.mul hinv
  rw [zero_mul] at hprod
  have h1 : Tendsto (fun z : ℝ => 1 - (Real.log ⌈z⌉₊ - Real.log z) * (Real.log ⌈z⌉₊)⁻¹)
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hprod
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  have h1 : (0 : ℝ) < z := by linarith
  have hlogz : Real.log z ≠ 0 := by
    have : 0 < Real.log z := Real.log_pos hz
    linarith
  have hlogc : Real.log (⌈z⌉₊ : ℝ) ≠ 0 := by
    have h2 : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
    have : 0 < Real.log (⌈z⌉₊ : ℝ) := Real.log_pos (by linarith)
    linarith
  rw [div_eq_mul_inv]
  field_simp
  ring

/-- Mertens' third theorem with the strict real cutoff `p < z`. -/
private lemma tendsto_prod_strict_mul_log :
    Tendsto (fun z : ℝ => (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log z)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hcomp : Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log ⌈z⌉₊)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) :=
    tendsto_prod_range_mul_log.comp tendsto_nat_ceil_atTop
  have hmain := hcomp.mul tendsto_log_div_log_ceil
  rw [mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  have hlogc : Real.log (⌈z⌉₊ : ℝ) ≠ 0 := by
    have h2 : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
    have : 0 < Real.log (⌈z⌉₊ : ℝ) := Real.log_pos (by linarith)
    linarith
  field_simp


/-- The truncated twin constant product tends to `twinC`. -/
private lemma tendsto_twin_truncation :
    Tendsto (fun z : ℝ => ∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
      (1 - 1 / ((p : ℝ) - 1) ^ 2)) atTop (𝓝 LeanLab.ChenExplicit.twinC) := by
  let s : Set ℕ := {p | p.Prime ∧ 2 < p}
  let f : ℕ → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2
  have hh : HasProd (s.mulIndicator f) LeanLab.ChenExplicit.twinC :=
    hasProd_subtype_iff_mulIndicator.mp LeanLab.ChenExplicit.twinC_multipliable.hasProd
  have ht := hh.tendsto_prod_nat.comp (tendsto_nat_ceil_atTop (α := ℝ))
  simpa only [s, f, Set.mulIndicator, prod_filter, Function.comp_def, Set.mem_ofPred_eq] using ht

/-- The odd-prime product factors through the ordinary and the twin products. -/
private lemma odd_product_factorization (z : ℝ) (hz : 2 < z) :
    (∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) =
    2 * (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) *
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  let P := (range ⌈z⌉₊).filter Nat.Prime
  let O := (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p)
  have htwo : 2 ∈ P := mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hz), by decide⟩
  have herase : P.erase 2 = O := by
    ext p
    simp only [P, O, mem_erase, mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hne, hpz, hp⟩
      exact ⟨hpz, hp, by have := hp.two_le; omega⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨by omega, hpz, hp⟩
  have hsplit : (∏ p ∈ O, (1 - 1 / (p : ℝ))) =
      2 * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    have hh := prod_erase_mul (s := P) (f := fun p : ℕ => 1 - 1 / (p : ℝ)) htwo
    rw [herase] at hh
    norm_num at hh
    simpa only [one_div] using
      (show (∏ p ∈ O, (1 - (p : ℝ)⁻¹)) = 2 * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) by linarith)
  calc (∏ p ∈ O, (1 - 1 / ((p : ℝ) - 1)))
      = ∏ p ∈ O, (1 - 1 / (p : ℝ)) * (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
        refine Finset.prod_congr rfl ?_
        intro p hp
        have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.2
        have h1 : (p : ℝ) ≠ 0 := by linarith
        have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
        have h3 : ((p : ℝ) - 1) ^ 2 ≠ 0 := by positivity
        field_simp
        ring
    _ = (∏ p ∈ O, (1 - 1 / (p : ℝ))) * ∏ p ∈ O, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
        Finset.prod_mul_distrib
    _ = (2 * ∏ p ∈ P, (1 - 1 / (p : ℝ))) * ∏ p ∈ O, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
        rw [hsplit]
    _ = 2 * (∏ p ∈ P, (1 - 1 / (p : ℝ))) * ∏ p ∈ O, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
        ring

/-- `∏_{2<p<z}(1 - 1/(p-1)) · log z` tends to `2 e^{-γ} twinC`. -/
private lemma tendsto_base_prod_mul_log :
    Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) * Real.log z) atTop
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC)) := by
  have hA := tendsto_prod_strict_mul_log
  have hT := tendsto_twin_truncation
  have h := (hA.const_mul 2).mul hT
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with z hz
  rw [odd_product_factorization z hz]
  ring

/-- The normalized base product tends to one. -/
private lemma tendsto_base_prod_normalized :
    Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) * Real.log z /
        (2 * Real.exp (-Real.eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC)) atTop
      (𝓝 1) := by
  have hc : 2 * Real.exp (-Real.eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC ≠ 0 := by
    have := LeanLab.ChenExplicit.twinC_pos
    positivity
  have h := (tendsto_base_prod_mul_log).div_const (2 * Real.exp (-Real.eulerMascheroniConstant)
    * LeanLab.ChenExplicit.twinC)
  rw [div_self hc] at h
  exact h


/-- Monotonicity of a product of naturals. -/
private lemma prod_le_prod_nat {s : Finset ℕ} {f g : ℕ → ℕ} (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact Nat.mul_le_mul (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Monotonicity of a product of nonnegative reals. -/
private lemma prod_le_prod_real {s : Finset ℕ} {f g : ℕ → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hga : 0 ≤ g a :=
        le_trans hfa (h a (Finset.mem_insert_self a s))
      exact mul_le_mul (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))) hfs hga

/-- At most twelve prime divisors of `N` reach the lower cutoff `N ^ kappa1`. -/
private lemma tail_card_le (N : ℕ) (hN : 2 ≤ N) :
    #(N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ))) ≤ 12 := by
  classical
  set T := N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)) with hT
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmem : ∀ p ∈ T, p.Prime ∧ p ∣ N ∧ (2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)) := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := Finset.mem_filter.mp hp
    exact ⟨(Nat.mem_primeFactors.mp hp1).1, (Nat.mem_primeFactors.mp hp1).2.1, hp2, hp3⟩
  have hsub : T ⊆ N.primeFactors := Finset.filter_subset _ _
  have hdvd : ∏ p ∈ T, p ∣ N :=
    (Finset.prod_dvd_prod_of_subset T N.primeFactors (fun p : ℕ => p) hsub).trans
      N.prod_primeFactors_dvd
  have hle : ∏ p ∈ T, p ≤ N := Nat.le_of_dvd (by omega) hdvd
  have h12 : ∀ p ∈ T, N ≤ p ^ 12 := by
    intro p hp
    obtain ⟨-, -, -, hpz⟩ := hmem p hp
    have h1 : ((N : ℝ) ^ kappa1) ^ 12 ≤ ((p : ℝ)) ^ 12 :=
      pow_le_pow_left₀ (by positivity) hpz 12
    have h2 : ((N : ℝ) ^ kappa1) ^ 12 = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hNpos)]
      norm_num [kappa1]
    rw [h2] at h1
    have h3 : ((p ^ 12 : ℕ) : ℝ) = ((p : ℝ)) ^ 12 := by push_cast; ring
    rw [← h3] at h1
    exact_mod_cast h1
  have hkey : N ^ #T ≤ (∏ p ∈ T, p) ^ 12 := by
    calc N ^ #T = ∏ _p ∈ T, N := (Finset.prod_const N).symm
      _ ≤ ∏ p ∈ T, p ^ 12 := prod_le_prod_nat fun p hp => h12 p hp
      _ = (∏ p ∈ T, p) ^ 12 := Finset.prod_pow ..
  have hfin : N ^ #T ≤ N ^ 12 :=
    hkey.trans (Nat.pow_le_pow_left hle 12)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < N)).mp hfin

/-- Every value of the tail correction is at least one. -/
private lemma tailCorrection_ge_one (N : ℕ) :
    1 ≤ ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
      (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  refine Finset.one_le_prod₀ fun p hp => ?_
  have h2 : (3 : ℝ) ≤ p := by
    have := (Finset.mem_filter.mp hp).2.1
    exact_mod_cast (show 3 ≤ p by omega)
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The tail correction tends to one. -/
private lemma tendsto_tailCorrection :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primeFactors.filter
        (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
      (((p : ℝ) - 1) / ((p : ℝ) - 2))) atTop (𝓝 1) := by
  classical
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have hz2 : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1 - 2) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-2) hz
    simpa only [sub_eq_add_neg] using h
  have hinv0 : Tendsto (fun N : ℕ => ((N : ℝ) ^ kappa1 - 2)⁻¹) atTop (𝓝 0) :=
    hz2.inv_tendsto_atTop
  have hinv : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ kappa1 - 2)) atTop (𝓝 0) := by
    simpa only [one_div] using hinv0
  have hupper : Tendsto (fun N : ℕ => (1 + 1 / ((N : ℝ) ^ kappa1 - 2)) ^ 12) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).pow 12
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards with N
    exact tailCorrection_ge_one N
  · filter_upwards [hz.eventually (eventually_ge_atTop (4 : ℝ)), eventually_ge_atTop 2] with N hz4 hN
    have hpos : (0 : ℝ) < (N : ℝ) ^ kappa1 - 2 := by linarith
    have hterm : ∀ p ∈ N.primeFactors.filter
        (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
        (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ 1 + 1 / ((N : ℝ) ^ kappa1 - 2) := by
      intro p hp
      obtain ⟨-, hp2, hpz⟩ := Finset.mem_filter.mp hp
      have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
      have hpz' : (N : ℝ) ^ kappa1 ≤ (p : ℝ) := by exact_mod_cast hpz
      have hle : 1 / ((p : ℝ) - 2) ≤ 1 / ((N : ℝ) ^ kappa1 - 2) :=
        one_div_le_one_div_of_le hpos (by linarith)
      have heq : ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := by
        field_simp
        ring
      rw [heq]
      linarith
    have hcard := tail_card_le N hN
    have hnonneg : ∀ p ∈ N.primeFactors.filter
        (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
        0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
      intro p hp
      have hp2 : (2 : ℝ) < p := by
        have := (Finset.mem_filter.mp hp).2.1
        exact_mod_cast this
      have : 0 < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        apply div_pos <;> linarith
      linarith
    calc ∏ p ∈ N.primeFactors.filter
          (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2))
        ≤ ∏ _p ∈ N.primeFactors.filter
            (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
            (1 + 1 / ((N : ℝ) ^ kappa1 - 2)) :=
          prod_le_prod_real hnonneg hterm
      _ = (1 + 1 / ((N : ℝ) ^ kappa1 - 2)) ^ #(N.primeFactors.filter
            (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ))) := Finset.prod_const _
      _ ≤ (1 + 1 / ((N : ℝ) ^ kappa1 - 2)) ^ 12 :=
          pow_le_pow_right₀ (by
            have h : (0 : ℝ) ≤ 1 / ((N : ℝ) ^ kappa1 - 2) := by positivity
            linarith) hcard


/-- The sieve primes below the cutoff are the odd primes below it not dividing `N`. -/
private lemma PS_eq_filter (N : ℕ) (hEven : Even N) :
    Wu41.PS N 0 ((N : ℝ) ^ kappa1)
      = (range ⌈(N : ℝ) ^ kappa1⌉₊).filter
          (fun p : ℕ => p.Prime ∧ 2 < p ∧ ¬ p ∣ N) := by
  ext p
  rw [Wu41.mem_PS]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, -, hpz, hcop⟩
    refine ⟨Nat.lt_ceil.mpr hpz, hp, ?_, (hp.coprime_iff_not_dvd.mp hcop)⟩
    have hne : p ≠ 2 := by
      rintro rfl
      exact (hp.coprime_iff_not_dvd.mp hcop) hEven.two_dvd
    have := hp.two_le
    omega
  · rintro ⟨hpz, hp, hp2, hndvd⟩
    exact ⟨hp, by positivity, Nat.lt_ceil.mp hpz, hp.coprime_iff_not_dvd.mpr hndvd⟩

/-- The prime divisors inside the cutoff. -/
private lemma filter_dvd_eq_small (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
    ((range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p)).filter (fun p => p ∣ N)
      = N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hpz, hp, hp2⟩, hdvd⟩
    exact ⟨⟨hp, hdvd, by omega⟩, hp2, Nat.lt_ceil.mp hpz⟩
  · rintro ⟨⟨hp, hdvd, -⟩, hp2, hpz⟩
    exact ⟨⟨Nat.lt_ceil.mpr hpz, hp, hp2⟩, hdvd⟩

/-- `(1 - 1/(p-1)) (p-1)/(p-2) = 1` for `p > 2`. -/
private lemma local_factor_mul (p : ℕ) (hp : 2 < p) :
    (1 - 1 / ((p : ℝ) - 1)) * (((p : ℝ) - 1) / ((p : ℝ) - 2)) = 1 := by
  have h2 : (2 : ℝ) < p := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- The local density is the whole odd product times the small singular correction. -/
private lemma lowerDensity_eq_base_mul_small (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
    lowerDensity N
      = (∏ p ∈ (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
            (1 - 1 / ((p : ℝ) - 1))) *
        ∏ p ∈ N.primeFactors.filter
            (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  classical
  set S := (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p) with hS
  set Ss := N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1) with hSs
  have hV : lowerDensity N
      = ∏ p ∈ (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => (p.Prime ∧ 2 < p) ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1)) := by
    unfold lowerDensity
    rw [PS_eq_filter N hEven]
    refine Finset.prod_congr ?_ (fun p _ => rfl)
    exact Finset.filter_congr fun p _ => by tauto
  have hnot : S.filter (fun p => ¬ p ∣ N)
      = (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => (p.Prime ∧ 2 < p) ∧ ¬ p ∣ N) := by
    rw [hS, Finset.filter_filter]
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := S) (p := fun p : ℕ => p ∣ N)
    (f := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1))
  have hsmall : S.filter (fun p => p ∣ N) = Ss := filter_dvd_eq_small N hN hEven
  rw [hsmall] at hsplit
  have hgh : (∏ p ∈ Ss, (1 - 1 / ((p : ℝ) - 1))) *
      (∏ p ∈ Ss, (((p : ℝ) - 1) / ((p : ℝ) - 2))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun p hp => local_factor_mul p (Finset.mem_filter.mp hp).2.1
  have hP1 : (∏ p ∈ Ss, (1 - 1 / ((p : ℝ) - 1)))
      = (∏ p ∈ Ss, (((p : ℝ) - 1) / ((p : ℝ) - 2)))⁻¹ :=
    eq_inv_of_mul_eq_one_left hgh
  have hP1ne : (∏ p ∈ Ss, (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≠ 0 := by
    have hpos : ∀ p ∈ Ss, (0 : ℝ) < (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
      intro p hp
      have hp2 : (2 : ℝ) < p := by
        have := (Finset.mem_filter.mp hp).2.1
        exact_mod_cast this
      apply div_pos <;> linarith
    exact ne_of_gt (Finset.prod_pos hpos)
  have hmain : (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1)))
      = (∏ p ∈ Ss, (((p : ℝ) - 1) / ((p : ℝ) - 2)))⁻¹ * lowerDensity N := by
    rw [← hsplit, hP1, hnot, ← hV]
  rw [hmain]
  field_simp

/-- The singular factor splits into the small correction and the tail. -/
private lemma oddFactor_eq_small_mul_tail (N : ℕ) :
    oddFactor N
      = (∏ p ∈ N.primeFactors.filter
            (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1),
          (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
        ∏ p ∈ N.primeFactors.filter
            (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  classical
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (s := N.primeFactors.filter (fun p : ℕ => 2 < p))
    (p := fun p : ℕ => (p : ℝ) < (N : ℝ) ^ kappa1)
    (f := fun p : ℕ => (((p : ℝ) - 1) / ((p : ℝ) - 2)))
  have e1 : (N.primeFactors.filter (fun p : ℕ => 2 < p)).filter
      (fun p : ℕ => (p : ℝ) < (N : ℝ) ^ kappa1)
      = N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1) := by
    rw [Finset.filter_filter]
  have e2 : (N.primeFactors.filter (fun p : ℕ => 2 < p)).filter
      (fun p : ℕ => ¬ (p : ℝ) < (N : ℝ) ^ kappa1)
      = N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun p _ => ?_
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, not_lt.mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, not_lt.mpr h2⟩
  unfold oddFactor
  rw [e1, e2] at hsplit
  exact hsplit.symm


/-- The exact factorization of the normalized density. -/
private lemma scaledDensity_mul_tail (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
    scaledDensity N * (∏ p ∈ N.primeFactors.filter
        (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
        (((p : ℝ) - 1) / ((p : ℝ) - 2)))
      = Real.log N * (∏ p ∈ (range ⌈(N : ℝ) ^ kappa1⌉₊).filter
            (fun p : ℕ => p.Prime ∧ 2 < p), (1 - 1 / ((p : ℝ) - 1))) /
          LeanLab.ChenExplicit.twinC := by
  classical
  have hV := lowerDensity_eq_base_mul_small N hN hEven
  have hO := oddFactor_eq_small_mul_tail N
  have hsmall_pos : ∀ p ∈ N.primeFactors.filter
      (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1),
      (0 : ℝ) < (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    intro p hp
    have hp2 : (2 : ℝ) < p := by
      have := (Finset.mem_filter.mp hp).2.1
      exact_mod_cast this
    apply div_pos <;> linarith
  have hP1ne : (∏ p ∈ N.primeFactors.filter
      (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1),
      (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≠ 0 :=
    ne_of_gt (Finset.prod_pos hsmall_pos)
  have hP2ne : (∏ p ∈ N.primeFactors.filter
      (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
      (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≠ 0 := by
    have := tailCorrection_ge_one N
    linarith
  have hTne : LeanLab.ChenExplicit.twinC ≠ 0 := LeanLab.ChenExplicit.twinC_pos.ne'
  unfold scaledDensity CN
  rw [hV, hO]
  field_simp

set_option maxHeartbeats 1000000 in
/-- LEAF. Wu 2004 page 38, the Euler product asymptotic before equation 10.2.
Only the local density is normalized. No sieve count occurs here. -/
theorem scaledDensity_tendsto :
    Tendsto scaledDensity evenAtTop (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant))) := by
  classical
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have htail := tendsto_tailCorrection
  -- the strict-cutoff base product composed with the cutoff sequence
  have hbase := tendsto_base_prod_mul_log.comp hz
  -- replace `log (N ^ kappa1)` by `kappa1 * log N`
  have hlogrpow : ∀ᶠ N : ℕ in atTop, Real.log ((N : ℝ) ^ kappa1) = kappa1 * Real.log N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.log_rpow hpos]
  have hA : Tendsto (fun N : ℕ =>
      (∏ p ∈ (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) * Real.log N) atTop
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC / kappa1)) := by
    have h2 := hbase.div_const kappa1
    refine h2.congr' ?_
    filter_upwards [hlogrpow] with N hN
    simp only [Function.comp_apply]
    rw [hN]
    have hk : kappa1 ≠ 0 := by norm_num [kappa1]
    field_simp
  have hf : Tendsto (fun N : ℕ =>
      (∏ p ∈ (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) * Real.log N / LeanLab.ChenExplicit.twinC) atTop
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / kappa1)) := by
    have h2 := hA.div_const LeanLab.ChenExplicit.twinC
    have hlim : 2 * Real.exp (-Real.eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC / kappa1
        / LeanLab.ChenExplicit.twinC = 2 * Real.exp (-Real.eulerMascheroniConstant) / kappa1 := by
      have hk : kappa1 ≠ 0 := by norm_num [kappa1]
      have hT : LeanLab.ChenExplicit.twinC ≠ 0 := LeanLab.ChenExplicit.twinC_pos.ne'
      field_simp
    rw [hlim] at h2
    exact h2
  have hquot := hf.div htail (by norm_num : (1 : ℝ) ≠ 0)
  rw [div_one] at hquot
  -- pass to the even numbers
  have hquot' := tendsto_inf_left (x₂ := principal {N : ℕ | Even N}) hquot
  have hL : 2 * Real.exp (-Real.eulerMascheroniConstant) / kappa1
      = 2 / (kappa1 * Real.exp Real.eulerMascheroniConstant) := by
    rw [Real.exp_neg]
    field_simp
  rw [hL] at hquot'
  refine hquot'.congr' ?_
  have hevEven : ∀ᶠ N : ℕ in evenAtTop, Even N := by
    rw [evenAtTop, Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall fun N h => h
  filter_upwards [hevEven, (eventually_ge_atTop 2).filter_mono inf_le_left] with N hEven hN
  have h := scaledDensity_mul_tail N hN hEven
  have htailne : (∏ p ∈ N.primeFactors.filter
      (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
      (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≠ 0 := by
    have := tailCorrection_ge_one N
    linarith
  dsimp only [Pi.div_apply]
  refine (div_eq_iff htailne).mpr ?_
  rw [mul_comm ((∏ p ∈ (range ⌈(N : ℝ) ^ kappa1⌉₊).filter
    (fun p : ℕ => p.Prime ∧ 2 < p), (1 - 1 / ((p : ℝ) - 1)))) (Real.log N)]
  exact h.symm

/-- LEAF. Wu 2004 page 38, Lemmas 2.2 and 2.3 before equation 10.2.
The finite level lower sieve estimate precedes the Euler product normalization.
The replacement of li N by N over log N is included in the normalized error. -/
theorem main0_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main0 f B N - η * Θ N ≤ sieveTerms N 0 := by
  sorry

/-- The finite main term has the required coefficient limit.
CONDITIONAL ON the OPEN Euler product asymptotic and IsLinearSieve. -/
theorem main0_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    Tendsto (fun N => main0 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 0)) := by
  have hc : ContinuousAt f (6 : ℝ) := h.2.1.continuousAt (Ioi_mem_nhds (by norm_num))
  have hf : Tendsto (fun N => f (lowerLevel B N 1)) evenAtTop (𝓝 (f 6)) :=
    hc.tendsto.comp (tendsto_inf_left (lowerLevel_one_tendsto B))
  have ht := scaledDensity_tendsto.mul hf
  have ht' : Tendsto (fun N => scaledDensity N * f (lowerLevel B N 1))
      evenAtTop (𝓝 (integralTerms F f ω 0)) := by
    convert ht using 1
    change 𝓝 (2 * f (1 / (2 * kappa1)) / (kappa1 * exp eulerMascheroniConstant)) = _
    congr 1
    rw [show (1 / (2 * kappa1) : ℝ) = 6 by norm_num [kappa1]]
    ring
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main0_ratio f B hN).symm

/-- Two independent half epsilon errors give the final normalized lower bound.
This is an elementary assembly with the analytic inputs explicit. -/
theorem lower_of_main (c : ℝ) (u : ℕ → ℝ) (main : ℝ → ℕ → ℝ)
    (hsieve : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N → main B N - η * Θ N ≤ u N)
    (hlimit : ∀ B : ℝ, 0 < B →
      Tendsto (fun N => main B N / Θ N) evenAtTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (c - ε) * Θ N ≤ u N := by
  intro ε hε
  obtain ⟨B, hB, M, hM⟩ := hsieve (ε / 2) (by positivity)
  have he : ∀ᶠ N in evenAtTop, c - ε / 2 < main B N / Θ N :=
    (hlimit B hB).eventually (eventually_gt_nhds (by linarith : c - ε / 2 < c))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_inf_principal.1 he)
  refine ⟨max 2 (max M K), ?_⟩
  intro N hEven hN
  have ht := Θ_pos (show 2 ≤ N by omega)
  have hc := (lt_div_iff₀ ht).1 (hK N (by omega) hEven)
  have hs := hM N hEven (by omega)
  nlinarith

/-- The exact lower_F0 conclusion follows from two strictly smaller leaves.
OPEN through main0_lower and scaledDensity_tendsto. -/
theorem lower_F0_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 := by
  exact lower_of_main _ _ (main0 f) (main0_lower F f h)
    (fun B _ => main0_tendsto F f ω h B)

end LeanLab.ChenDoubleSieve.Task348
