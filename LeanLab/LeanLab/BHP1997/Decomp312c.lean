/-
P0069, pages 24 to 27. CODEX task312.
The generic Perron input has no sieve construction or density conclusion.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165
import LeanLab.BHP1997.Thm4Statement
import LeanLab.PNTPort.ExplicitPsi1.Residues

namespace LeanLab.BHP1997.Decomp312c
open Classical Complex DecompC165b
open scoped BigOperators

/-- Page 24, the reference width y1 below display 4.2. -/
noncomputable def referenceWidth (x : ℝ) : ℝ :=
  x * Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ))

/-- Pages 24 and 25, the character average on I1 used in the repaired 4.2. -/
noncomputable def referenceAverage (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
    (a x k : ℂ) * χ (k : ZMod q)) / (referenceWidth x : ℂ)

/-- Page 24, display 4.1 with both signs of height as required by the
Perron contour on page 25. This is a paper statement for reviewer inspection. -/
def MeanValue41 (ε : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ σ ∈ ({-1, 1} : Finset ℝ),
      (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖) ≤
        C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)

/-- Pages 24 to 27, the mild arithmetic requirement separated from 4.1.
The normalized I1 average has density delta times u over log x with every
logarithmic saving. This is a paper statement for reviewer inspection. -/
def ReferenceDensity (u : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖referenceAverage a x χ - Thm2.delta χ * u / Real.log x‖ ≤
        C * Real.log x ^ (-A)

/-- Page 25, display 4.5 applied to the two suffixes defining a prefix of I.
Center by the I1 average. This retains the factor 2Y for the full interval I.
This is a paper statement for reviewer inspection. -/
def RelativeDistribution (ε : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, t ≤ x →
      ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- Page 25, display 4.5 after comparison with y1 and finite centering.
Include widths below 2 by the divisor bound. The x power absorbs endpoint
rounding. This is a paper statement for reviewer inspection. -/
def WindowComparison (ε : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 0 ≤ y → y ≤ referenceWidth x →
      ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊,
        ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ ≤
        C * (y * Real.log x ^ (-A) + x ^ (0.55 + 11 * ε / 12))

/-- Page 3, condition i, display 1.7, for a real coefficient family.
This is a paper statement for reviewer inspection. -/
def CharacterDistribution (ε u : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, t ≤ x →
      ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - Thm2.delta χ * u / Real.log x)‖ ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- Pages 26 and 27, the absolute truncation error controlled by 4.11
and 4.12. The actual sifted coefficients and the auxiliary mean-value
coefficients agree on I up to every logarithmic saving.
This is a paper statement for reviewer inspection. -/
def ShortApproximation (ε : ℝ) (a b : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    (∑ k ∈ leftInterval ε x, |a x k - b x k|) ≤
      C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- The reference width is positive whenever x is positive. This is the
elementary denominator fact needed by the Perron comparison. -/
theorem referenceWidth_pos {x : ℝ} (hx : 0 < x) : 0 < referenceWidth x := by
  rw [referenceWidth]
  positivity

/-- For x at least 1, the reference width is at most x. This is the
elementary size bound needed before placing the reference interval inside I1. -/
theorem referenceWidth_le_x {x : ℝ} (hx : 1 ≤ x) : referenceWidth x ≤ x := by
  rw [referenceWidth]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp : 0 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.rpow_nonneg hl _
  have h3 : 0 ≤ 3 * Real.log x ^ (1 / 3 : ℝ) :=
    mul_nonneg (by norm_num) hp
  have he : -3 * Real.log x ^ (1 / 3 : ℝ) ≤ 0 := by linarith
  have hexp : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) ≤ 1 := by
    have h := Real.exp_le_exp.mpr he
    rwa [Real.exp_zero] at h
  simpa using mul_le_mul_of_nonneg_left hexp (zero_le_one.trans hx)

/-- For x at least 3, the reference width is less than x divided by 2.
This places every permitted window above the lower endpoint of I1. -/
theorem referenceWidth_lt_half_x {x : ℝ} (hx : 3 ≤ x) : referenceWidth x < x / 2 := by
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).2
    exact le_of_lt (Real.exp_one_lt_d9.trans
      (show (2.7182818286 : ℝ) < 3 by norm_num)) |>.trans hx
  have hL : 1 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
  have hexp1 : 2 < Real.exp 1 := by
    exact (show (2 : ℝ) < 2.7182818283 by norm_num).trans Real.exp_one_gt_d9
  have hsquare : 4 < (Real.exp 1) ^ 2 := by nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have hcube : 8 < (Real.exp 1) ^ 3 := by
    nlinarith [mul_pos (by nlinarith : 0 < (Real.exp 1) ^ 2) (by nlinarith : 0 < Real.exp 1)]
  have hexp3 : 2 < Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith
  have hexpneg : Real.exp (-3) < 1 / 2 := by
    rw [Real.exp_neg]
    have h := (inv_lt_inv₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 2)).2 hexp3
    simpa using h
  have h3L : 3 ≤ 3 * Real.log x ^ (1 / 3 : ℝ) := by
    calc
      3 = 3 * 1 := by norm_num
      _ ≤ 3 * Real.log x ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 3 by norm_num)
  have harg : -3 * Real.log x ^ (1 / 3 : ℝ) ≤ -3 := by linarith
  have hfactor : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) ≤ Real.exp (-3) :=
    Real.exp_le_exp.mpr harg
  rw [referenceWidth]
  have hmul := mul_lt_mul_of_pos_left (lt_of_le_of_lt hfactor hexpneg) hx0
  have hdiv : x / 2 = x * (1 / 2) := by field_simp
  rw [hdiv]
  exact hmul

/-- Every permitted Perron window is contained in the long interval I1 when
x is at least 3. This is the geometric containment used by the contour step. -/
theorem window_subset_I1 {x y : ℝ} (hx : 3 ≤ x) (hy : 0 ≤ y)
    (hyw : y ≤ referenceWidth x) :
    Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ ⊆
      Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊ := by
  have hwidth := referenceWidth_lt_half_x hx
  have hbounds : 0 ≤ y ∧ y ≤ referenceWidth x := ⟨hy, hyw⟩
  have hreal : x / 2 ≤ x - y := by linarith [hbounds.1, hbounds.2, hwidth]
  have hlo : ⌊x / 2⌋₊ ≤ ⌊x - y⌋₊ := Nat.floor_mono hreal
  have hhi : ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := Nat.floor_mono (by linarith)
  intro k hk
  rw [Finset.mem_Ioc] at hk ⊢
  exact ⟨lt_of_le_of_lt hlo hk.1, le_trans hk.2 hhi⟩


/-- Page 5 coefficient input, the divisor count is bounded by every positive power. -/
private theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hc (p : ℕ) : 1 ≤ c p := by dsimp [c]; split_ifs <;> linarith
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)


/-- Pages 11 and 12, increasing a divisor exponent preserves a zero-at-zero coefficient bound. -/
private theorem coeffBound_mono {a : ℕ → ℂ} {B D : ℝ} (ha0 : a 0 = 0)
    (ha : Thm4.CoeffBound a B) (hBD : B ≤ D) : Thm4.CoeffBound a D := by
  intro n
  by_cases hn : n = 0
  · subst n; rw [ha0, norm_zero]; positivity
  have ht : 1 ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  exact (ha n).trans (Real.rpow_le_rpow_of_exponent_le ht hBD)

/-- Pages 11 and 12, a positive-power divisor bound gives positive-power coefficient growth. -/
private theorem coeff_small_power
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    : ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ δ := by
  have hB1 : 0 < B + 1 := by linarith
  obtain ⟨C, hC, hbound⟩ := card_divisors_le_rpow (ε := δ / (B + 1)) (div_pos hδ hB1)
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


/-- Pages 11 and 12, positive-index small-power growth holds for every real divisor exponent. -/
private theorem coeff_small_power_any (B δ : ℝ) (hδ : 0 < δ) :
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

/-- Pages 24 and 25, I is eventually shorter than the reference interval I1. -/
private theorem reference_width_long {ε : ℝ} (hε : ε < 1 / 10) :
    ∀ᶠ x : ℝ in Filter.atTop, 2 * x ^ (11 / 20 + ε) ≤ referenceWidth x := by
  let δ : ℝ := (0.45 - ε) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hs : ∀ᶠ t : ℝ in Filter.atTop, t ^ (-(2 / 3 : ℝ)) < δ / 3 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually
      (eventually_lt_nhds (div_pos hδ (by norm_num)))
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (Real.log 2 / δ)),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx2 hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (1 / 3 : ℝ) = Real.log x * Real.log x ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + (-(2 / 3 : ℝ))) := by norm_num
      _ = _ := by rw [Real.rpow_add hl, Real.rpow_one]
  have hsmall : 3 * Real.log x ^ (1 / 3 : ℝ) ≤ δ * Real.log x := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hx.le hl.le]
  have hlog2 : Real.log 2 ≤ δ * Real.log x := by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hx2
  have htot : Real.log 2 + (11 / 20 + ε) * Real.log x ≤
      Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ) := by
    dsimp [δ] at hsmall hlog2
    linarith
  rw [referenceWidth, Real.rpow_def_of_pos (show 0 < x by linarith)]
  calc
    2 * Real.exp (Real.log x * (11 / 20 + ε)) =
        Real.exp (Real.log 2 + (11 / 20 + ε) * Real.log x) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ Real.exp (Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ)) := Real.exp_le_exp.mpr htot
    _ = _ := by
      rw [show Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ) =
        Real.log x + -3 * Real.log x ^ (1 / 3 : ℝ) by ring,
        Real.exp_add, Real.exp_log (show 0 < x by linarith)]


/-- Page 25, the number of integer terms differs from a suffix width by at most one. -/
private theorem suffix_card_error {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    |((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) - y| ≤ 1 := by
  have hx : 0 ≤ x := hy.trans hyx
  have hxy : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hfloor : ⌊x - y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
  rw [Nat.card_Ioc, Nat.cast_sub hfloor, abs_le]
  have h1 := Nat.floor_le hx
  have h2 := Nat.floor_le hxy
  have h3 := Nat.lt_floor_add_one x
  have h4 := Nat.lt_floor_add_one (x - y)
  constructor <;> linarith

/-- Page 25, the reference average is bounded by twice a bound on its coefficients.
The extra factor accounts for integer endpoint rounding. -/
private theorem suffix_average_bound (f : ℕ → ℂ) {x w M : ℝ}
    (hw : 1 ≤ w) (hwx : w ≤ x) (hM : 0 ≤ M)
    (hf : ∀ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, ‖f k‖ ≤ M) :
    ‖(∑ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f k) / (w : ℂ)‖ ≤ 2 * M := by
  have hw0 : 0 < w := by linarith
  have hc := (abs_le.mp (suffix_card_error (by linarith : 0 ≤ w) hwx)).2
  have hs : ‖∑ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f k‖ ≤
      ((Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊).card : ℝ) * M := by
    exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum hf)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
  apply (div_le_iff₀ hw0).mpr
  nlinarith

/-- Page 25, separate finite centering from the comparison with a continuous width. -/
private theorem finite_centering_bound (S : Finset ℕ) (f : ℕ → ℂ) (r E : ℂ) (y : ℝ) (hy : 0 ≤ y) :
    ‖∑ k ∈ S, (f k - r)‖ ≤
      ‖(∑ k ∈ S, f k) - (y : ℂ) * E‖ +
        y * ‖E - r‖ + |(S.card : ℝ) - y| * ‖r‖ := by
  have he : (∑ k ∈ S, (f k - r)) =
      ((∑ k ∈ S, f k) - (y : ℂ) * E) +
        (y : ℂ) * (E - r) + ((y : ℂ) - S.card) * r := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ‖((∑ k ∈ S, f k) - (y : ℂ) * E) + (y : ℂ) * (E - r)‖ +
        ‖((y : ℂ) - S.card) * r‖ := norm_add_le _ _
    _ ≤ (‖(∑ k ∈ S, f k) - (y : ℂ) * E‖ + ‖(y : ℂ) * (E - r)‖) +
        ‖((y : ℂ) - S.card) * r‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by
      rw [norm_mul, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [show ((y : ℂ) - S.card) = ((y - (S.card : ℝ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      rw [abs_of_nonneg hy]

/-- Page 25, display 4.5 at y and the reference width implies finite centering.
Widths below two use only the coefficient bound. -/
private theorem center_from_continuous_comparison (f : ℕ → ℂ) (E : ℂ)
    {x w C L P M : ℝ} (hw : 2 ≤ w) (hwx : w ≤ x)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hf : ∀ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, ‖f k‖ ≤ M)
    (hcomp : ∀ z : ℝ, 2 ≤ z → z ≤ w →
      ‖(∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, f k) - (z : ℂ) * E‖ ≤
        C * (z * L + P))
    {y : ℝ} (hy : 0 ≤ y) (hyw : y ≤ w) :
    ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊,
      (f k - (∑ j ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f j) / (w : ℂ))‖ ≤
        2 * C * (y * L + P) + 9 * M := by
  let r : ℂ := (∑ j ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f j) / (w : ℂ)
  have hw0 : 0 < w := by linarith
  have hr : ‖r‖ ≤ 2 * M := suffix_average_bound f (by linarith) hwx hM hf
  have hyx : y ≤ x := hyw.trans hwx
  have hsub : Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ ⊆ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊ := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.floor_mono (by linarith)) hkl, hku⟩
  have hc := suffix_card_error hy hyx
  by_cases hy2 : 2 ≤ y
  · have hdist : ‖E - r‖ ≤ C * (w * L + P) / w := by
      have he : E - r = -((∑ j ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f j) - (w : ℂ) * E) / (w : ℂ) := by
        dsimp [r]
        field_simp [show (w : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hw0]
        ring
      rw [he, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
      exact div_le_div_of_nonneg_right (hcomp w hw le_rfl) hw0.le
    have hydiv : y / w ≤ 1 := (div_le_one hw0).mpr hyw
    have hrem : y * ‖E - r‖ ≤ C * (y * L + P) := by
      calc
        _ ≤ y * (C * (w * L + P) / w) := mul_le_mul_of_nonneg_left hdist hy
        _ = C * (y * L + y / w * P) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_of_le_one_left hP hydiv)) hC
    have hround : |((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) - y| * ‖r‖ ≤ 2 * M := by
      calc
        _ ≤ 1 * ‖r‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ ≤ _ := by simpa using hr
    have hfin := finite_centering_bound (Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊) f r E y hy
    have hwin := hcomp y hy2 hyw
    change ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (f k - r)‖ ≤ _
    linarith
  · have hc3 : ((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) ≤ 3 := by
      have := (abs_le.mp hc).2
      linarith
    have hs : ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (f k - r)‖ ≤
        ((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) * (3 * M) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, 3 * M := by
          apply Finset.sum_le_sum
          intro k hk
          have hkM := hf k (hsub hk)
          have ht := norm_sub_le (f k) r
          linarith
        _ = _ := by simp
    have hp : 0 ≤ 2 * C * (y * L + P) := by positivity
    have hm : ((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) * (3 * M) ≤ 9 * M := by
      nlinarith
    exact hs.trans (by linarith)

/-- Page 25, the Perron window kernel is bounded uniformly over every height.
The bound uses only that the window stays above x divided by two. -/
private theorem perron_kernel_bound {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyx : y ≤ x / 2) (t : ℝ) :
    ‖((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t‖ ≤
      (x / 2) ^ (-(1 / 2 : ℝ)) * y := by
  let s : ℂ := Thm4.half t
  have hs : s ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp [s, Thm4.half] at hre
  have hxy : 0 < x - y := by linarith
  have hd : ∀ u ∈ Set.Icc (x - y) x,
      HasDerivWithinAt (fun v : ℝ => (v : ℂ) ^ s / s)
        ((u : ℂ) ^ (s - 1)) (Set.Icc (x - y) x) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hxy.trans_le hu.1)
    have hr : s - 1 ≠ -1 := by intro h; apply hs; linear_combination h
    simpa only [sub_add_cancel] using
      (hasDerivAt_ofReal_cpow_const' hu0 hr).hasDerivWithinAt
  have hb : ∀ u ∈ Set.Ico (x - y) x,
      ‖(u : ℂ) ^ (s - 1)‖ ≤ (x / 2) ^ (-(1 / 2 : ℝ)) := by
    intro u hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hxy.trans_le hu.1)]
    have hre : (s - 1).re = -(1 / 2 : ℝ) := by simp [s, Thm4.half]; norm_num
    rw [hre]
    apply Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2) (by linarith [hu.1] : x / 2 ≤ u)
    norm_num
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb x
    (show x ∈ Set.Icc (x - y) x from ⟨by linarith, le_rfl⟩)
  simpa only [← sub_div, sub_sub_cancel] using h

/-- Page 25, both high height pieces are bounded by the same kernel estimate.
This is the integral bookkeeping used with the two signs in display 4.1. -/
private theorem two_tail_norm_bound (F K : ℝ → ℂ) (hF : Continuous F) (hK : Continuous K)
    {T0 T1 R M : ℝ} (hT : T0 ≤ T1) (hR : 0 ≤ R)
    (hkernel : ∀ t : ℝ, ‖K t‖ ≤ R)
    (hplus : (∫ t in T0..T1, ‖F t‖) ≤ M)
    (hminus : (∫ t in T0..T1, ‖F (-t)‖) ≤ M) :
    ‖(∫ t in (-T1)..T1, F t * K t) -
      ∫ t in (-T0)..T0, F t * K t‖ ≤ 2 * R * M := by
  have hprod : Continuous (fun t => F t * K t) := hF.mul hK
  have hbound {a b : ℝ} (hab : a ≤ b) :
      ‖∫ t in a..b, F t * K t‖ ≤ R * ∫ t in a..b, ‖F t‖ := by
    calc
      _ ≤ ∫ t in a..b, R * ‖F t‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab
        · exact Filter.Eventually.of_forall (fun t ht => by
            rw [norm_mul]
            simpa only [mul_comm] using
              mul_le_mul_of_nonneg_left (hkernel t) (norm_nonneg (F t)))
        · exact (continuous_const.mul hF.norm).intervalIntegrable _ _
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hp := (hbound hT).trans (mul_le_mul_of_nonneg_left hplus hR)
  have hn : ‖∫ t in (-T1)..(-T0), F t * K t‖ ≤ R * M := by
    have he : (∫ t in (-T1)..(-T0), ‖F t‖) = ∫ t in T0..T1, ‖F (-t)‖ := by
      exact (intervalIntegral.integral_comp_neg (fun t => ‖F t‖) (a := T0) (b := T1)).symm
    exact (hbound (neg_le_neg hT)).trans
      (mul_le_mul_of_nonneg_left (he.trans_le hminus) hR)
  rw [intervalIntegral.integral_interval_sub_interval_comm'
    (hprod.intervalIntegrable _ _) (hprod.intervalIntegrable _ _) (hprod.intervalIntegrable _ _),
    intervalIntegral.integral_symm (-T1) (-T0), sub_neg_eq_add]
  have hnorm := norm_add_le
    (∫ t in T0..T1, F t * K t) (∫ t in (-T1)..(-T0), F t * K t)
  linarith

/-- Pages 24 and 25, the subexponential low height is eventually below every
fixed positive power height. -/
private theorem eventually_low_height_le_power {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ α := by
  have hs : ∀ᶠ u : ℝ in Filter.atTop, u ^ (-(2 / 3 : ℝ)) < α :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually
      (eventually_lt_nhds hα)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (1 / 3 : ℝ) = Real.log x * Real.log x ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + (-(2 / 3 : ℝ))) := by norm_num
      _ = _ := by rw [Real.rpow_add hl, Real.rpow_one]
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  apply Real.exp_le_exp.mpr
  rw [he]
  exact mul_le_mul_of_nonneg_left hx.le hl.le

/-- Page 25, the first order expansion of the Perron window kernel.
This is the pointwise Taylor error used in display 4.4. -/
private theorem perron_kernel_first_order_bound {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyx : y ≤ x / 2) (t : ℝ) :
    ‖((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t -
      (y : ℂ) * (x : ℂ) ^ (Thm4.half t - 1)‖ ≤
        ‖Thm4.half t - 1‖ * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 := by
  let s : ℂ := Thm4.half t
  let H : ℝ := ‖s - 1‖ * (x / 2) ^ (-(3 / 2 : ℝ))
  have hs : s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [s, Thm4.half] at h'
  have hr : s - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [s, Thm4.half] at h'
    norm_num at h'
  have hxy : 0 < x - y := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hbound {u v : ℝ} (hu : x - y ≤ u) (hv : u ≤ v) :
      ‖(s - 1) * (v : ℂ) ^ (s - 1 - 1)‖ ≤ H := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < v)]
    have hre : (s - 1 - 1).re = -(3 / 2 : ℝ) := by simp [s, Thm4.half]; norm_num
    rw [hre]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2)
      (by linarith : x / 2 ≤ v) (by norm_num)
  have hfirst : ∀ u ∈ Set.Icc (x - y) x,
      ‖(u : ℂ) ^ (s - 1) - (x : ℂ) ^ (s - 1)‖ ≤ H * y := by
    intro u hu
    have hd : ∀ v ∈ Set.Icc u x,
        HasDerivWithinAt (fun v : ℝ => (v : ℂ) ^ (s - 1))
          ((s - 1) * (v : ℂ) ^ (s - 1 - 1)) (Set.Icc u x) v := by
      intro v hv
      exact (hasDerivAt_ofReal_cpow_const (by linarith [hu.1, hv.1] : v ≠ 0) hr).hasDerivWithinAt
    have hb : ∀ v ∈ Set.Ico u x,
        ‖(s - 1) * (v : ℂ) ^ (s - 1 - 1)‖ ≤ H := by
      intro v hv
      exact hbound hu.1 hv.1
    have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hb x
      (show x ∈ Set.Icc u x from ⟨hu.2, le_rfl⟩)
    rw [norm_sub_rev] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hu.1]) hH)
  let g : ℝ → ℂ := fun u => (u : ℂ) ^ s / s - (u : ℂ) * (x : ℂ) ^ (s - 1)
  have hd : ∀ u ∈ Set.Icc (x - y) x,
      HasDerivWithinAt g ((u : ℂ) ^ (s - 1) - (x : ℂ) ^ (s - 1))
        (Set.Icc (x - y) x) u := by
    intro u hu
    have h0 : u ≠ 0 := by linarith [hu.1]
    have hn : s - 1 ≠ -1 := by intro h; apply hs; linear_combination h
    have hpower := hasDerivAt_ofReal_cpow_const' h0 hn
    have hlinear := ((hasDerivAt_id u).ofReal_comp).mul_const ((x : ℂ) ^ (s - 1))
    simpa only [g, Pi.sub_apply, id_eq, sub_add_cancel, Complex.ofReal_one, one_mul] using!
      (hpower.sub hlinear).hasDerivWithinAt
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun u hu => hfirst u (Set.Ico_subset_Icc_self hu)) x
    (show x ∈ Set.Icc (x - y) x from ⟨by linarith, le_rfl⟩)
  have he : g x - g (x - y) =
      ((x : ℂ) ^ s - ((x - y : ℝ) : ℂ) ^ s) / s -
        (y : ℂ) * (x : ℂ) ^ (s - 1) := by
    dsimp [g]
    push_cast
    ring
  rw [he] at hh
  simpa only [sub_sub_cancel, H, pow_two, mul_assoc] using hh

/-- Page 25, the low height exceeds every fixed power of log x eventually.
This is the logarithmic absorption used in display 4.4. -/
private theorem eventually_log_power_le_low_height (D : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ D ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) := by
  have hs : ∀ᶠ u : ℝ in Filter.atTop, D * Real.log u ≤ u ^ (1 / 3 : ℝ) := by
    filter_upwards [((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul_left D).bound
      (by norm_num : (0 : ℝ) < 1), Filter.eventually_ge_atTop (0 : ℝ)] with u hu hu0
    have h : |D * Real.log u| ≤ u ^ (1 / 3 : ℝ) := by
      simpa only [one_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hu0 _)] using hu
    exact (le_abs_self _).trans h
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with x hx hx0
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Page 24, the finite polynomial F on the long coefficient support. -/
private noncomputable def criticalPolynomial (a : ℝ → ℕ → ℝ) (x t : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
    (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t

/-- Page 25, the vertical Perron integral in display 4.3.
The real parametrization cancels the factor i from ds. -/
private noncomputable def windowContour (a : ℝ → ℕ → ℝ) (x y T : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
    criticalPolynomial a x t χ *
      (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t)

/-- Page 25, the common low height center E below display 4.4. -/
private noncomputable def lowCenter (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in (-(Real.exp (Real.log x ^ (1 / 3 : ℝ))))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
      criticalPolynomial a x t χ * (x : ℂ) ^ (Thm4.half t - 1)

/-! ### Truncated Perron kernel at abscissa `1/2`

Ported from `Routes/Decomp1551a.perron_kernel_bound` (abscissa `2`) and
`DERZ1997/Perron136.perron_rescale`, with `perronI` inlined, then rescaled to `1/2`.
Uses exactly one added import, `LeanLab.PNTPort.ExplicitPsi1.Residues`
(6 files in its closure, 0 `sorry`). -/
open Filter Topology MeasureTheory Set
open scoped Topology
open LeanLab.PNTPort.ExplicitPsi1

set_option maxHeartbeats 2000000 in
/-- Truncated Perron kernel at abscissa `2` (Davenport, ch. 17, the discontinuous integral). -/
private theorem perron_kernel_two (y : ℝ) (hy : 0 < y) (hy1 : y ≠ 1) (T : ℝ) (hT : 0 < T) :
    ‖((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I))
      - (if 1 < y then 1 else 0)‖ ≤ y ^ 2 / (Real.pi * T * |Real.log y|) := by
  let F : ℂ → ℂ := fun s => (y : ℂ) ^ s / s
  let H : ℝ → ℝ → ℝ → ℂ := fun a b v => ∫ σ in a..b, F ((σ : ℂ) + v * I)
  let V : ℝ → ℂ := fun a => ∫ t in (-T)..T, F ((a : ℂ) + t * I)
  have hF : ∀ s : ℂ, s ≠ 0 → AnalyticAt ℂ F s := by
    intro s hs
    exact (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hy s).div analyticAt_id hs
  have hn : ∀ σ v : ℝ, |v| = T → ‖F ((σ : ℂ) + v * I)‖ ≤ y ^ σ / T := by
    intro σ v hv
    dsimp [F]
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hy]
    have hd : T ≤ ‖(σ : ℂ) + v * I‖ := by
      have hh := abs_im_le_norm ((σ : ℂ) + v * I)
      simpa [hv] using hh
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) hT hd
  have hnear : (F - fun s : ℂ => 1 / (s - 0)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    have hd := (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl (ofReal_ne_zero.mpr hy.ne'))
    have hh := hd.tendsto_slope_zero
    simp only [id_eq, zero_add, cpow_zero, mul_one, one_mul, smul_eq_mul] at hh
    have he : (F - fun s : ℂ => 1 / (s - 0)) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun s => s⁻¹ * ((y : ℂ) ^ s - 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      dsimp [F]
      field_simp
      ring
    exact (hh.congr' he.symm).isBigO_one ℂ
  have hrectL : ∀ a : ℝ, a < 0 → RectangleIntegral' F ⟨a, -T⟩ ⟨2, T⟩ = 1 := by
    intro a ha
    apply ResidueTheoremOnRectangleWithSimplePole' (p := 0) (A := 1)
    · simp; linarith
    · simp; linarith
    · rw [rectangle_mem_nhds_iff]
      simp only [mem_reProdIm, zero_re, zero_im, uIoo_of_le (by linarith : a ≤ 2),
        uIoo_of_le (by linarith : -T ≤ T), mem_Ioo]
      exact ⟨⟨ha, by norm_num⟩, by linarith, hT⟩
    · intro s hs
      exact (hF s hs.2).differentiableAt.differentiableWithinAt
    · exact hnear
  have hrectR : ∀ b : ℝ, 2 ≤ b → RectangleIntegral' F ⟨2, -T⟩ ⟨b, T⟩ = 0 := by
    intro b hb
    have hf : HolomorphicOn F (Rectangle (⟨2, -T⟩ : ℂ) ⟨b, T⟩) := by
      intro s hs
      apply (hF s ?_).differentiableAt.differentiableWithinAt
      intro hz
      simp only [Rectangle, mem_reProdIm, uIcc_of_le (by linarith : (2 : ℝ) ≤ b)] at hs
      have hh := hs.1.1
      rw [hz] at hh
      norm_num at hh
    simp only [RectangleIntegral', hf.vanishesOnRectangle (by rfl), smul_zero]
  have hhl : ∀ a : ℝ, a ≤ 2 → 1 < y → ∀ v : ℝ, |v| = T →
      ‖H a 2 v‖ ≤ y ^ 2 / (T * Real.log y) := by
    intro a ha hyy v hv
    have hdom : IntegrableOn (fun σ : ℝ => y ^ σ / T) (Iic 2) := by
      have hh := (integrableOn_exp_mul_Iic (Real.log_pos hyy) 2).div_const T
      simpa [IntegrableOn, Real.rpow_def_of_pos hy, mul_comm] using hh
    have hsub : Ioc a (2 : ℝ) ⊆ Iic 2 := fun _ h => h.2
    have hh := norm_integral_le_of_norm_le (hdom.mono_set hsub) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with σ hσ
      exact hn σ v hv)
    have hh' := setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun σ => by dsimp; positivity))
      (Filter.Eventually.of_forall hsub)
    have he : (∫ σ in Iic (2 : ℝ), y ^ σ / T) = y ^ 2 / (T * Real.log y) := by
      simp_rw [Real.rpow_def_of_pos hy]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const]
      have he : (fun σ : ℝ => Real.exp (Real.log y * σ)) = (fun σ : ℝ => Real.exp (σ * Real.log y)) := by funext σ; rw [mul_comm]
      rw [integral_exp_mul_Iic (Real.log_pos hyy)]
      rw [← Real.rpow_def_of_pos hy, Real.rpow_two]
      ring
    have hh0 : ‖H a 2 v‖ ≤ ∫ σ in Ioc a 2, y ^ σ / T := by
      simpa [H, intervalIntegral.integral_of_le ha] using hh
    exact hh0.trans (hh'.trans_eq he)
  have hhr : ∀ b : ℝ, 2 ≤ b → y < 1 → ∀ v : ℝ, |v| = T →
      ‖H 2 b v‖ ≤ y ^ 2 / (T * -Real.log y) := by
    intro b hb hyy v hv
    have hl : Real.log y < 0 := Real.log_neg hy hyy
    have hdom : IntegrableOn (fun σ : ℝ => y ^ σ / T) (Ioi 2) := by
      have hh := (integrableOn_exp_mul_Ioi hl 2).div_const T
      simpa [IntegrableOn, Real.rpow_def_of_pos hy, mul_comm] using hh
    have hsub : Ioc (2 : ℝ) b ⊆ Ioi 2 := fun _ h => h.1
    have hh := norm_integral_le_of_norm_le (hdom.mono_set hsub) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with σ hσ
      exact hn σ v hv)
    have hh' := setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun σ => by dsimp; positivity))
      (Filter.Eventually.of_forall hsub)
    have he : (∫ σ in Ioi (2 : ℝ), y ^ σ / T) = y ^ 2 / (T * -Real.log y) := by
      simp_rw [Real.rpow_def_of_pos hy]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const]
      have he : (fun σ : ℝ => Real.exp (Real.log y * σ)) = (fun σ : ℝ => Real.exp (σ * Real.log y)) := by funext σ; rw [mul_comm]
      rw [integral_exp_mul_Ioi hl]
      rw [← Real.rpow_def_of_pos hy, Real.rpow_two]
      ring
    have hh0 : ‖H 2 b v‖ ≤ ∫ σ in Ioc 2 b, y ^ σ / T := by
      simpa [H, intervalIntegral.integral_of_le hb] using hh
    exact hh0.trans (hh'.trans_eq he)
  have hV : ∀ a : ℝ, 1 ≤ |a| → ‖V a‖ ≤ 2 * T * y ^ a := by
    intro a ha
    have hh : ∀ t ∈ Set.uIoc (-T) T, ‖F ((a : ℂ) + t * I)‖ ≤ y ^ a := by
      intro t _
      have hd : 1 ≤ ‖(a : ℂ) + t * I‖ := by
        have h := abs_re_le_norm ((a : ℂ) + t * I)
        have hre : ((a : ℂ) + t * I).re = a := by simp
        rw [hre] at h
        exact ha.trans h
      dsimp [F]
      rw [norm_div, norm_cpow_eq_rpow_re_of_pos hy]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact div_le_self (Real.rpow_nonneg hy.le _) hd
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hh
    have he : |T - -T| = 2 * T := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
    rw [he] at h
    exact h.trans_eq (by ring)
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have hcI : c * I = ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    dsimp [c]
    push_cast
    field_simp
  have hcn : ‖c‖ = 1 / (2 * Real.pi) := by
    simp [c, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_div]
  have hsc : (1 / (2 * Real.pi) : ℂ) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
    push_cast
    rw [one_div]
  have hpK : ((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
      (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I)) = c * I * V 2 := by
    rw [hcI, hsc]
    rfl
  let D : ℝ := y ^ 2 / (T * |Real.log y|)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  rcases lt_or_gt_of_ne hy1 with hyy | hyy
  · simp only [not_lt.mpr hyy.le, ↓reduceIte, sub_zero]
    have hl : Real.log y < 0 := Real.log_neg hy hyy
    have hhs : ∀ b : ℝ, 2 ≤ b → ∀ v : ℝ, |v| = T → ‖H 2 b v‖ ≤ D := by
      intro b hb v hv
      simpa [D, abs_of_neg hl] using hhr b hb hyy v hv
    have hbound : ∀ n : ℕ,
        ‖((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
          (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I))‖ ≤
          (2 * T * y ^ ((n : ℝ) + 3) + 2 * D) / (2 * Real.pi) := by
      intro n
      let b : ℝ := n + 3
      have hb : 2 ≤ b := by dsimp [b]; have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hId := hrectR b hb
      have hId : c * (H 2 b (-T) - H 2 b T + I * V b - I * V 2) = 0 := by
        simpa only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
          smul_eq_mul, one_div, c, H, V] using hId
      have he : ((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
          (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I)) =
          c * (H 2 b (-T) - H 2 b T + I * V b) := by
        rw [hpK]
        linear_combination -hId
      have hnorm : ‖H 2 b (-T) - H 2 b T + I * V b‖ ≤
          ‖H 2 b (-T)‖ + ‖H 2 b T‖ + ‖V b‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (by simp))
      have hv := hV b (by rw [abs_of_nonneg (by linarith)]; linarith)
      have hh1 := hhs b hb (-T) (by rw [abs_neg, abs_of_pos hT])
      have hh2 := hhs b hb T (abs_of_pos hT)
      rw [he, norm_mul, hcn]
      calc
        _ ≤ (1 / (2 * Real.pi)) * (D + D + 2 * T * y ^ b) := by gcongr; linarith
        _ = _ := by dsimp [b]; ring
    have hp : Tendsto (fun n : ℕ => y ^ ((n : ℝ) + 3)) atTop (𝓝 0) := by
      have he : ∀ n : ℕ, y ^ ((n : ℝ) + 3) = y ^ n * y ^ (3 : ℕ) := by
        intro n
        rw [Real.rpow_add hy, Real.rpow_natCast]
        norm_cast
      simp_rw [he]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hy.le hyy).mul_const (y ^ 3)
    have hh := ((hp.const_mul (2 * T)).add_const (2 * D)).div_const (2 * Real.pi)
    have hfinal : (0 + 2 * D) / (2 * Real.pi) = y ^ 2 / (Real.pi * T * |Real.log y|) := by
      dsimp [D]
      field_simp
      ring
    simp only [mul_zero] at hh
    rw [hfinal] at hh
    exact ge_of_tendsto' hh hbound
  · simp only [hyy, ↓reduceIte]
    have hl : 0 < Real.log y := Real.log_pos hyy
    have hhs : ∀ a : ℝ, a ≤ 2 → ∀ v : ℝ, |v| = T → ‖H a 2 v‖ ≤ D := by
      intro a ha v hv
      simpa [D, abs_of_pos hl] using hhl a ha hyy v hv
    have hbound : ∀ n : ℕ,
        ‖((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
          (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I)) - 1‖ ≤
          (2 * T * y ^ (-((n : ℝ) + 1)) + 2 * D) / (2 * Real.pi) := by
      intro n
      let a : ℝ := -((n : ℝ) + 1)
      have ha : a < 0 := by dsimp [a]; have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hId := hrectL a ha
      have hId : c * (H a 2 (-T) - H a 2 T + I * V 2 - I * V a) = 1 := by
        simpa only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
          smul_eq_mul, one_div, c, H, V] using hId
      have he : ((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
          (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I)) - 1 =
          c * (I * V a - H a 2 (-T) + H a 2 T) := by
        rw [hpK]
        linear_combination hId
      have hnorm : ‖I * V a - H a 2 (-T) + H a 2 T‖ ≤
          ‖V a‖ + ‖H a 2 (-T)‖ + ‖H a 2 T‖ := by
        exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (by simp)) le_rfl)
      have hv := hV a (by rw [abs_of_neg ha]; dsimp [a]; have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hh1 := hhs a (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT])
      have hh2 := hhs a (by linarith) T (abs_of_pos hT)
      rw [he, norm_mul, hcn]
      calc
        _ ≤ (1 / (2 * Real.pi)) * (2 * T * y ^ a + D + D) := by gcongr; linarith
        _ = _ := by dsimp [a]; ring
    have hp : Tendsto (fun n : ℕ => y ^ (-((n : ℝ) + 1))) atTop (𝓝 0) := by
      have he : ∀ n : ℕ, y ^ (-((n : ℝ) + 1)) = (y⁻¹) ^ n * y⁻¹ := by
        intro n
        rw [Real.rpow_neg hy.le, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_one,
          mul_inv, inv_pow]
      simp_rw [he]
      have hiy : y⁻¹ < 1 := (inv_lt_one₀ hy).mpr hyy
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hy.le) hiy).mul_const y⁻¹
    have hh := ((hp.const_mul (2 * T)).add_const (2 * D)).div_const (2 * Real.pi)
    have hfinal : (0 + 2 * D) / (2 * Real.pi) = y ^ 2 / (Real.pi * T * |Real.log y|) := by
      dsimp [D]
      field_simp
      ring
    simp only [mul_zero] at hh
    rw [hfinal] at hh
    exact ge_of_tendsto' hh hbound

set_option maxHeartbeats 1000000 in
/-- Rescaling identity: the Perron kernel at abscissa `c` is the kernel at abscissa `2`
along `y ↦ y ^ (c/2)`, `T ↦ T / (c/2)`. -/
private theorem perron_rescale_general {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
      = (1 / (2 * Real.pi) : ℂ) * ∫ u in (-(T / (c / 2)))..(T / (c / 2)),
          ((y ^ (c / 2) : ℝ) : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I) := by
  let a : ℝ := c / 2
  let z : ℝ := y ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hy a
  have hpower (u : ℝ) :
      (y : ℂ) ^ ((c : ℂ) + ((a * u : ℝ) : ℂ) * I) =
        (z : ℂ) ^ ((2 : ℂ) + u * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne')]
    rw [← Complex.ofReal_log hy.le, ← Complex.ofReal_log hz.le]
    dsimp [z]
    rw [Real.log_rpow hy]
    push_cast
    congr 1
    dsimp [a]
    push_cast
    ring
  have hden (u : ℝ) : (c : ℂ) + ((a * u : ℝ) : ℂ) * I =
      (a : ℂ) * ((2 : ℂ) + u * I) := by
    dsimp [a]
    push_cast
    ring
  have hterm (u : ℝ) : (a : ℂ) *
      ((y : ℂ) ^ ((c : ℂ) + ((a * u : ℝ) : ℂ) * I) /
        ((c : ℂ) + ((a * u : ℝ) : ℂ) * I)) =
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I) := by
    rw [hpower, hden, ← mul_div_assoc]
    exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr ha.ne')
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  have hs := intervalIntegral.smul_integral_comp_mul_left (a := -T / a) (b := T / a) f a
  have hl : a * (-T / a) = -T := by field_simp
  have hr : a * (T / a) = T := by field_simp
  rw [hl, hr] at hs
  have heq : (∫ u : ℝ in (-T / a)..(T / a),
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I)) =
      ∫ t : ℝ in (-T)..T, f t := by
    calc
      _ = ∫ u : ℝ in (-T / a)..(T / a), (a : ℂ) * f (a * u) := by
        apply intervalIntegral.integral_congr
        intro u _
        exact (hterm u).symm
      _ = (a : ℂ) * ∫ u : ℝ in (-T / a)..(T / a), f (a * u) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [← Complex.real_smul]; exact hs
  show (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, f t) =
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ in (-(T / a))..(T / a),
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I)
  rw [← neg_div, heq]

set_option maxHeartbeats 1000000 in
/-- Truncated Perron kernel at the abscissa `1/2`, the shape used by `windowContour`. -/
private theorem perron_kernel_half {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {T : ℝ} (hT : 0 < T) :
    ‖((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))
      - (if 1 < y then 1 else 0)‖ ≤ y ^ (1 / 2 : ℝ) / (Real.pi * T * |Real.log y|) := by
  have h4 : (0 : ℝ) < 1 / 2 := by norm_num
  have hT4 : (0 : ℝ) < T / ((1 / 2 : ℝ) / 2) := by positivity
  have hz0 : (0 : ℝ) < y ^ ((1 / 2 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
  have hz4 : (y ^ ((1 / 2 : ℝ) / 2)) ^ 4 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
  have hz1 : y ^ ((1 / 2 : ℝ) / 2) ≠ 1 := by
    intro h
    apply hy1
    rw [← hz4, h, one_pow]
  have hiff : (1 < y ^ ((1 / 2 : ℝ) / 2)) ↔ (1 < y) := by
    constructor
    · intro h
      have h4' : 1 < (y ^ ((1 / 2 : ℝ) / 2)) ^ 4 := one_lt_pow₀ h (by norm_num)
      rwa [hz4] at h4'
    · intro h
      have h4' : 1 < (y ^ ((1 / 2 : ℝ) / 2)) ^ 4 := by rwa [hz4]
      by_contra hle
      push_neg at hle
      have h1 : (y ^ ((1 / 2 : ℝ) / 2)) ^ 4 ≤ 1 ^ 4 :=
        pow_le_pow_left₀ hz0.le hle 4
      rw [one_pow] at h1
      linarith
  -- the rescaled expression and its bound
  set B : ℂ := (1 / (2 * Real.pi) : ℂ) * ∫ u in (-(T / ((1 / 2 : ℝ) / 2)))..(T / ((1 / 2 : ℝ) / 2)),
      ((y ^ ((1 / 2 : ℝ) / 2) : ℝ) : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I) with hB
  have hres : (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
      (y : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I) = B := by
    rw [hB]
    simpa using perron_rescale_general (y := y) (c := (1 / 2 : ℝ)) (T := T) hy h4
  have hkey := perron_kernel_two (y := y ^ ((1 / 2 : ℝ) / 2)) hz0 hz1
    (T := T / ((1 / 2 : ℝ) / 2)) hT4
  have hdir : (if 1 < y ^ ((1 / 2 : ℝ) / 2) then (1 : ℂ) else 0) = (if 1 < y then 1 else 0) := by
    by_cases h : 1 < y ^ ((1 / 2 : ℝ) / 2)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hy' => h (hiff.mpr hy'))]
  rw [hdir] at hkey
  have hzsq : (y ^ ((1 / 2 : ℝ) / 2)) ^ 2 = y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
  have hzlog : Real.log (y ^ ((1 / 2 : ℝ) / 2)) = (1 / 2 : ℝ) / 2 * Real.log y :=
    Real.log_rpow hy _
  have hT' : T / ((1 / 2 : ℝ) / 2) = 4 * T := by field_simp; norm_num
  have hbound : (y ^ ((1 / 2 : ℝ) / 2)) ^ 2 /
      (Real.pi * (T / ((1 / 2 : ℝ) / 2)) * |Real.log (y ^ ((1 / 2 : ℝ) / 2))|)
      ≤ y ^ (1 / 2 : ℝ) / (Real.pi * T * |Real.log y|) := by
    rw [hzsq, hzlog, abs_mul, show |(1 / 2 : ℝ) / 2| = 1 / 4 by norm_num, hT']
    have hne : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
    have hL : |Real.log y| ≠ 0 := abs_ne_zero.mpr hne
    have hTne : T ≠ 0 := ne_of_gt hT
    have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    norm_num
  have hkey' : ‖B - (if 1 < y then 1 else 0)‖ ≤ y ^ (1 / 2 : ℝ) / (Real.pi * T * |Real.log y|) :=
    hkey.trans hbound
  simpa only [← hres] using hkey'

/-! ### Near-cutoff crude bound for the same kernel

Where `perron_kernel_half` degenerates (integers `k` with `T |log(x/k)| < 1`) the
kernel is only bounded crudely; this supplies the `O(log T)` bound used there. -/

/-- `∫_0^T (1/2 + t)⁻¹ dt = log (2T+1)`. -/
private theorem integral_half_add_inv (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (1 / 2 + t)⁻¹ = Real.log (2 * T + 1) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => Real.log (1 / 2 + s)) (1 / 2 + t)⁻¹ t := by
    intro t ht
    have h0 : (0 : ℝ) ≤ t := by
      rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
    have hpos : (0 : ℝ) < 1 / 2 + t := by linarith
    have h2 : HasDerivAt Real.log ((1 / 2 + t)⁻¹) (1 / 2 + t) := Real.hasDerivAt_log hpos.ne'
    have h1 : HasDerivAt (fun s : ℝ => 1 / 2 + s) 1 t := (hasDerivAt_id t).const_add (1 / 2)
    have h3 : HasDerivAt (fun s : ℝ => Real.log (1 / 2 + s)) ((1 / 2 + t)⁻¹ * 1) t := h2.comp t h1
    rwa [mul_one] at h3
  have hcont : ContinuousOn (fun t : ℝ => (1 / 2 + t)⁻¹) (Set.uIcc (0 : ℝ) T) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht hzero
    have h0 : (0 : ℝ) ≤ t := by
      rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h1 : Real.log (1 / 2 + T) - Real.log (1 / 2) = Real.log (2 * T + 1) := by
    rw [← Real.log_div (by linarith : (1 / 2 + T) ≠ 0) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    congr 1
    field_simp
    ring
  rw [← h1]
  norm_num

set_option maxHeartbeats 1000000 in
/-- Uniform crude bound for the truncated Perron kernel at abscissa `1/2` on `[1/4,2]`. -/
private theorem perron_crude_half {w T : ℝ} (hw1 : 1 / 4 ≤ w) (hw2 : w ≤ 2) (hT : 1 ≤ T) :
    ‖(1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
        (w : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ 8 * (1 + Real.log T) := by
  have hw0 : 0 < w := by linarith
  have hT0 : 0 < T := by linarith
  have hw2' : w ^ (1 / 2 : ℝ) ≤ 2 := by
    calc w ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hw2 (by norm_num)
      _ ≤ 2 := by
          calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hpt : ∀ t : ℝ, ‖(w : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ w ^ (1 / 2 : ℝ) * (2 * (1 / 2 + |t|)⁻¹) := by
    intro t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hw0]
    have hre : ((((1 / 2 : ℝ) : ℂ) + t * I)).re = 1 / 2 := by simp
    rw [hre, div_eq_mul_inv]
    have hden : (1 / 2 + |t|) / 2 ≤ ‖(((1 / 2 : ℝ) : ℂ) + t * I)‖ := by
      have h1 : |t| ≤ ‖(((1 / 2 : ℝ) : ℂ) + t * I)‖ := by
        simpa using abs_im_le_norm (((1 / 2 : ℝ) : ℂ) + t * I)
      have h2 : (1 / 2 : ℝ) ≤ ‖(((1 / 2 : ℝ) : ℂ) + t * I)‖ := by
        simpa using abs_re_le_norm (((1 / 2 : ℝ) : ℂ) + t * I)
      linarith
    have hd0 : 0 < (1 / 2 + |t|) / 2 := by positivity
    have h2 : ((1 / 2 + |t|) / 2)⁻¹ = 2 * (1 / 2 + |t|)⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    have h' : (‖(((1 / 2 : ℝ) : ℂ) + t * I)‖)⁻¹ ≤ 2 * (1 / 2 + |t|)⁻¹ := by
      rw [← one_div]
      calc 1 / ‖(((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 1 / ((1 / 2 + |t|) / 2) :=
            one_div_le_one_div_of_le hd0 hden
        _ = 2 * (1 / 2 + |t|)⁻¹ := by rw [one_div, h2]
    exact mul_le_mul_of_nonneg_left h' (Real.rpow_nonneg hw0.le _)
  have hcont : Continuous fun t : ℝ => (2 * (1 / 2 + |t|)⁻¹ : ℝ) := by
    have h1 : Continuous fun t : ℝ => (1 / 2 + |t| : ℝ) := by fun_prop
    exact continuous_const.mul (Continuous.inv₀ h1 (fun t => by positivity))
  have hmaj : ∫ t in (-T)..T, (2 * (1 / 2 + |t|)⁻¹ : ℝ) = 4 * Real.log (2 * T + 1) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-T) 0) (hcont.intervalIntegrable 0 T)]
    have hneg : ∫ t in (-T)..0, (2 * (1 / 2 + |t|)⁻¹ : ℝ)
        = ∫ t in (0 : ℝ)..T, (2 * (1 / 2 + |t|)⁻¹ : ℝ) := by
      have h := intervalIntegral.integral_comp_neg (f := fun t : ℝ => (2 * (1 / 2 + |t|)⁻¹ : ℝ))
        (a := (0 : ℝ)) (b := T)
      have h' : ∫ x in (0 : ℝ)..T, (2 * (1 / 2 + |(-x)|)⁻¹ : ℝ)
          = ∫ x in (0 : ℝ)..T, (2 * (1 / 2 + |x|)⁻¹ : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [abs_neg]
      rw [h'] at h
      simpa using h.symm
    rw [hneg]
    have hpos : ∫ t in (0 : ℝ)..T, (2 * (1 / 2 + |t|)⁻¹ : ℝ) = 2 * Real.log (2 * T + 1) := by
      rw [intervalIntegral.integral_congr (g := fun t : ℝ => 2 * (1 / 2 + t)⁻¹) ?_]
      · rw [intervalIntegral.integral_const_mul, integral_half_add_inv T (by linarith)]
      · intro t ht
        have ht0 : (0 : ℝ) ≤ t := by
          rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
        show (2 * (1 / 2 + |t|)⁻¹ : ℝ) = 2 * (1 / 2 + t)⁻¹
        rw [abs_of_nonneg ht0]
    rw [hpos]
    ring
  have h1 : ‖∫ t in (-T)..T,
      (w : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ ∫ t in (-T)..T, w ^ (1 / 2 : ℝ) * (2 * (1 / 2 + |t|)⁻¹) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ ?_
    · filter_upwards with t ht
      exact hpt t
    · exact (continuous_const.mul hcont).intervalIntegrable _ _
  have h2 : ∫ t in (-T)..T, w ^ (1 / 2 : ℝ) * (2 * (1 / 2 + |t|)⁻¹)
      = w ^ (1 / 2 : ℝ) * (4 * Real.log (2 * T + 1)) := by
    rw [intervalIntegral.integral_const_mul, hmaj]
  have hlogpos : 0 ≤ Real.log (2 * T + 1) := by
    apply Real.log_nonneg
    linarith
  have hlog3 : Real.log (2 * T + 1) ≤ 3 + Real.log T := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log (4 * T) := by
      apply Real.log_le_log (by linarith)
      linarith
    have h2 : Real.log (4 * T) = Real.log 4 + Real.log T := Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    linarith
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hc]
  calc (1 / (2 * Real.pi)) * ‖∫ t in (-T)..T,
        (w : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ (1 / (2 * Real.pi)) * (w ^ (1 / 2 : ℝ) * (4 * Real.log (2 * T + 1))) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 * w ^ (1 / 2 : ℝ) / Real.pi) * Real.log (2 * T + 1) := by
        field_simp
        ring
    _ ≤ (2 * 2 / Real.pi) * Real.log (2 * T + 1) := by
        calc (2 * w ^ (1 / 2 : ℝ) / Real.pi) * Real.log (2 * T + 1)
            = (2 / Real.pi) * w ^ (1 / 2 : ℝ) * Real.log (2 * T + 1) := by ring
          _ ≤ (2 / Real.pi) * 2 * Real.log (2 * T + 1) := by
              apply mul_le_mul_of_nonneg_right _ hlogpos
              exact mul_le_mul_of_nonneg_left hw2' (by positivity)
          _ = (2 * 2 / Real.pi) * Real.log (2 * T + 1) := by ring
    _ ≤ 2 * Real.log (2 * T + 1) := by
        have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
        have hle : 2 * 2 / Real.pi ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        exact mul_le_mul_of_nonneg_right hle hlogpos
    _ ≤ 2 * (3 + Real.log T) := by
        exact mul_le_mul_of_nonneg_left hlog3 (by norm_num)
    _ ≤ 8 * (1 + Real.log T) := by
        have hlt : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
        linarith

/-! ### Ingredients of the near-cutoff count

`|log (1+s)| ≥ |s|/2` on `(-1,1]` and `min 1 (h/j) ≤ 2h/(h+j)`; these drive the
count of integers with `T|log(x/k)| < 1`. -/

/-- `|log (1+s)| ≥ |s|/2` on `(-1, 1]`. -/
private theorem log_one_add_abs_lower {s : ℝ} (hs1 : -1 < s) (hs2 : s ≤ 1) :
    |s| / 2 ≤ |Real.log (1 + s)| := by
  have hpos : (0 : ℝ) < 1 + s := by linarith
  rcases lt_or_ge 0 s with h | h
  · have h1 : Real.log (1 / (1 + s)) ≤ 1 / (1 + s) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (1 / (1 + s)) = -Real.log (1 + s) := by
      rw [Real.log_div (by norm_num) (ne_of_gt hpos), Real.log_one]
      ring
    have h3 : 1 / (1 + s) - 1 = -(s / (1 + s)) := by
      field_simp
      ring
    rw [h2, h3] at h1
    have h4 : s / (1 + s) ≤ Real.log (1 + s) := neg_le_neg_iff.mp h1
    have h5 : s / 2 ≤ s / (1 + s) := by
      apply div_le_div_of_nonneg_left h.le (by linarith) (by linarith)
    rw [abs_of_nonneg h.le, abs_of_nonneg (Real.log_nonneg (by linarith))]
    linarith
  · have h4 : Real.log (1 + s) ≤ s := by
      have hh := Real.log_le_sub_one_of_pos hpos
      linarith
    rcases lt_or_eq_of_le h with h6 | h6
    · have h5 : Real.log (1 + s) < 0 := by linarith
      rw [abs_of_neg h6, abs_of_neg h5]
      linarith
    · rw [h6]
      norm_num

/-- `min 1 (h/j) ≤ 2h/(h+j)` for `h > 0`, `j ≥ 0`. -/
private theorem min_one_div_le {h j : ℝ} (hh : 0 < h) (hj : 0 ≤ j) :
    min 1 (h / j) ≤ 2 * h / (h + j) := by
  have hd : 0 < h + j := by linarith
  rcases eq_or_lt_of_le hj with h0 | hj0
  · have hj0' : j = 0 := h0.symm
    rw [hj0', div_zero, min_eq_right (show (0:ℝ) ≤ 1 by norm_num)]
    positivity
  · rcases le_total h j with hle | hle
    · have h1 : h / j ≤ 1 := (div_le_one (by linarith)).mpr hle
      rw [min_eq_right h1]
      field_simp
      nlinarith
    · have h1 : 1 ≤ h / j := (one_le_div (by linarith)).mpr hle
      rw [min_eq_left h1]
      field_simp
      nlinarith

/-! ### The window contour as a finite sum of cut kernels

`windowContour` is a finite sum over the polynomial support; each summand is
`a x k χ k` times the difference of two truncated Perron kernels, at the cuts
`x` and `x - y`. -/

/-- Quotients of complex powers of positive reals. -/
private theorem cpow_div_cpow_of_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (s : ℂ) :
    (A : ℂ) ^ s / (B : ℂ) ^ s = ((A / B : ℝ) : ℂ) ^ s := by
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hAB : (0 : ℝ) < A / B := div_pos hA hB
  have h1 : Complex.log (A : ℂ) = (Real.log A : ℂ) := (Complex.ofReal_log hA.le).symm
  have h2 : Complex.log (B : ℂ) = (Real.log B : ℂ) := (Complex.ofReal_log hB.le).symm
  have h3 : Complex.log ((A / B : ℝ) : ℂ) = (Real.log (A / B) : ℂ) :=
    (Complex.ofReal_log hAB.le).symm
  have h4 : Real.log (A / B) = Real.log A - Real.log B := Real.log_div hA.ne' hB.ne'
  rw [Complex.cpow_def_of_ne_zero hAc, Complex.cpow_def_of_ne_zero hBc,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hAB.ne'), h1, h2, h3, h4]
  push_cast
  rw [← Complex.exp_sub]
  congr 1
  ring

/-- The truncated Perron kernel at abscissa `1/2` on a positive base is continuous. -/
private theorem perron_kernel_continuous {u : ℝ} (hu : 0 < u) :
    Continuous fun t : ℝ => (u : ℂ) ^ Thm4.half t / Thm4.half t := by
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  refine Continuous.div (hhalf.const_cpow (Or.inl (by exact_mod_cast hu.ne'))) hhalf ?_
  intro t ht
  have h := congrArg Complex.re ht
  simp [Thm4.half] at h

/-- The difference of two cut kernels divided by the polynomial weight is continuous. -/
private theorem cpow_half_diff_continuous {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {k : ℕ} (hk : k ≠ 0) :
    Continuous fun t : ℝ =>
      (((A : ℂ) ^ Thm4.half t - ((B : ℝ) : ℂ) ^ Thm4.half t) /
        ((k : ℂ) ^ Thm4.half t * Thm4.half t)) := by
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcA : Continuous fun t : ℝ => (A : ℂ) ^ Thm4.half t :=
    hhalf.const_cpow (Or.inl (by exact_mod_cast hA.ne'))
  have hcB : Continuous fun t : ℝ => ((B : ℝ) : ℂ) ^ Thm4.half t :=
    hhalf.const_cpow (Or.inl (by exact_mod_cast hB.ne'))
  have hck : Continuous fun t : ℝ => (k : ℂ) ^ Thm4.half t :=
    hhalf.const_cpow (Or.inl hkc)
  refine Continuous.div (hcA.sub hcB) (hck.mul hhalf) (fun t ht => ?_)
  have hkz : (k : ℂ) ^ Thm4.half t ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hkc]
    exact Complex.exp_ne_zero _
  have hs : Thm4.half t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Thm4.half] at hre
  exact mul_ne_zero hkz hs ht

/-- Multiplying a positive-base power by a nonzero integer power recovers the base power. -/
private theorem cpow_of_div_mul {A : ℝ} (hA : 0 < A) {k : ℕ} (hk : k ≠ 0) (s : ℂ) :
    ((A / k : ℝ) : ℂ) ^ s * (k : ℂ) ^ s = (A : ℂ) ^ s := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkc : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; ring
  have hne : ((k : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hkc]
    exact Complex.exp_ne_zero _
  rw [← hcast, ← cpow_div_cpow_of_pos hA hkpos s]
  exact div_mul_cancel₀ _ hne

set_option maxHeartbeats 2000000 in
/-- The window contour is the finite sum of the coefficient-weighted cut kernels. -/
private theorem windowContour_eq_sum (a : ℝ → ℕ → ℝ) {x y T : ℝ} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (hxy : 0 < x - y) :
    windowContour a x y T χ =
      ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) *
        (((1 / (2 * Real.pi) : ℂ) *
            ∫ t in (-T)..T, ((x / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t)
          - ((1 / (2 * Real.pi) : ℂ) *
            ∫ t in (-T)..T, (((x - y) / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t)) := by
  set S := Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊ with hSdef
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  -- the integrand is the sum of the per-term integrands
  have hpt : ∀ t : ℝ, criticalPolynomial a x t χ *
      (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t) =
      ∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) *
        (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) /
          ((k : ℂ) ^ Thm4.half t * Thm4.half t)) := by
    intro t
    unfold criticalPolynomial
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      have hh := (Finset.mem_Ioc.mp hk).1
      omega
    have hkc : (k : ℂ) ^ Thm4.half t ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hk0))
    field_simp
  have hint : ∀ k ∈ S, IntervalIntegrable (fun t : ℝ => (a x k : ℂ) * χ (k : ZMod q) *
      (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) /
        ((k : ℂ) ^ Thm4.half t * Thm4.half t))) MeasureTheory.volume (-T) T := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have hh := (Finset.mem_Ioc.mp hk).1
      omega
    exact (continuous_const.mul (cpow_half_diff_continuous hx hxy hk0)).intervalIntegrable _ _
  -- per-term evaluation
  have hper : ∀ k ∈ S,
      (∫ t in (-T)..T, (a x k : ℂ) * χ (k : ZMod q) *
        (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) /
          ((k : ℂ) ^ Thm4.half t * Thm4.half t)))
      = (a x k : ℂ) * χ (k : ZMod q) *
        ((∫ t in (-T)..T, ((x / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t)
          - ∫ t in (-T)..T, (((x - y) / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have hh := (Finset.mem_Ioc.mp hk).1
      omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hve : (0 : ℝ) < x - y := hxy
    have hpt2 : ∀ t : ℝ,
        (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) /
          ((k : ℂ) ^ Thm4.half t * Thm4.half t)) =
        (((x / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t -
          (((x - y) / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t) := by
      intro t
      have h1 : (x : ℂ) ^ Thm4.half t = ((x / k : ℝ) : ℂ) ^ Thm4.half t *
          (k : ℂ) ^ Thm4.half t := (cpow_of_div_mul hx hk0 (Thm4.half t)).symm
      have h2 : ((x - y : ℝ) : ℂ) ^ Thm4.half t =
          (((x - y) / k : ℝ) : ℂ) ^ Thm4.half t * (k : ℂ) ^ Thm4.half t :=
        (cpow_of_div_mul hve hk0 (Thm4.half t)).symm
      have hkc : (k : ℂ) ^ Thm4.half t ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hk0)]
        exact Complex.exp_ne_zero _
      have hs0 : Thm4.half t ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp [Thm4.half] at hre
      rw [h1, h2]
      field_simp
    simp only [hpt2]
    have hi1 : IntervalIntegrable
        (fun t : ℝ => ((x / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t)
        MeasureTheory.volume (-T) T :=
      (perron_kernel_continuous (div_pos hx hkpos)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable
        (fun t : ℝ => (((x - y) / k : ℝ) : ℂ) ^ Thm4.half t / Thm4.half t)
        MeasureTheory.volume (-T) T :=
      (perron_kernel_continuous (div_pos hve hkpos)).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hi1 hi2]
  unfold windowContour
  rw [intervalIntegral.integral_congr (fun t _ => hpt t),
    intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hper k hk]
  ring

/-- Crude uniform bound for the saturated part of the cut kernel. -/
private theorem perron_err_crude {w T : ℝ} (hw1 : 1 / 4 ≤ w) (hw2 : w ≤ 2) (hT : 1 ≤ T) :
    ‖((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        (w : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)))
      - (if 1 < w then 1 else 0)‖ ≤ 9 * (1 + Real.log T) := by
  have h1 := perron_crude_half hw1 hw2 hT
  have h2 : ‖(if 1 < w then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs with h
    · simp
    · simp
  have hT0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  calc
    ‖((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        (w : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)))
      - (if 1 < w then 1 else 0)‖
        ≤ ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
            (w : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))‖
          + ‖(if 1 < w then (1 : ℂ) else 0)‖ := norm_sub_le _ _
    _ ≤ 8 * (1 + Real.log T) + 1 := add_le_add h1 h2
    _ ≤ 9 * (1 + Real.log T) := by linarith

/-- The number of integers in a real interval. -/
private theorem card_le_of_forall_mem_Icc {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) {s : Finset ℕ}
    (h : ∀ k ∈ s, A ≤ (k : ℝ) ∧ (k : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B - A + 2 := by
  have hsub : s ⊆ Finset.Icc ⌊A⌋₊ ⌊B⌋₊ := by
    intro k hk
    obtain ⟨h1, h2⟩ := h k hk
    exact Finset.mem_Icc.mpr
      ⟨by exact_mod_cast (Nat.floor_le hA).trans h1, Nat.le_floor h2⟩
  have hcard := Finset.card_le_card hsub
  have hcN : (Finset.Icc ⌊A⌋₊ ⌊B⌋₊).card = ⌊B⌋₊ + 1 - ⌊A⌋₊ := Nat.card_Icc _ _
  have hle : ⌊A⌋₊ ≤ ⌊B⌋₊ + 1 := by
    have := Nat.floor_mono hAB
    omega
  have hcast : ((Finset.Icc ⌊A⌋₊ ⌊B⌋₊).card : ℝ) = (⌊B⌋₊ : ℝ) + 1 - ⌊A⌋₊ := by
    rw [hcN, Nat.cast_sub hle]
    push_cast
    ring
  have hle' : (s.card : ℝ) ≤ (Finset.Icc ⌊A⌋₊ ⌊B⌋₊).card := by exact_mod_cast hcard
  rw [hcast] at hle'
  have hB : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (hA.trans hAB)
  have hA' : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
  linarith

/-- A sum of inverse distances to a fixed integer is at most twice the harmonic sum. -/
private theorem sum_inv_abs_sub_le (N m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (|(k : ℝ) - (m : ℝ)|)⁻¹ ≤ 2 * (harmonic N : ℝ) := by
  have hleft : ∑ k ∈ Finset.Icc 1 (m - 1), (|(k : ℝ) - (m : ℝ)|)⁻¹ ≤ (harmonic N : ℝ) := by
    have hinj : Set.InjOn (fun k : ℕ => m - k) ↑(Finset.Icc 1 (m - 1)) := by
      intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have h1 : a ≤ m := by omega
      have h2 : b ≤ m := by omega
      have hab' : m - a = m - b := hab
      calc a = m - (m - a) := (Nat.sub_sub_self h1).symm
        _ = m - (m - b) := by rw [hab']
        _ = b := Nat.sub_sub_self h2
    have hmap : Finset.image (fun k : ℕ => m - k) (Finset.Icc 1 (m - 1)) ⊆
        Finset.Icc 1 N := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    have hmain := Finset.sum_le_sum_of_injOn
      (f := fun k : ℕ => (|(k : ℝ) - (m : ℝ)|)⁻¹)
      (g := fun j : ℕ => ((j : ℝ))⁻¹) (fun k : ℕ => m - k) hinj hmap ?_ ?_
    · calc ∑ k ∈ Finset.Icc 1 (m - 1), (|(k : ℝ) - (m : ℝ)|)⁻¹
          ≤ ∑ j ∈ Finset.Icc 1 N, ((j : ℝ))⁻¹ := hmain
        _ = (harmonic N : ℝ) := by
            rw [harmonic_eq_sum_Icc]
            simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hkm : k ≤ m := by omega
      have hkr : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
      have habs : |(k : ℝ) - (m : ℝ)| = ((m - k : ℕ) : ℝ) := by
        rw [abs_of_nonpos (by linarith : (k : ℝ) - (m : ℝ) ≤ 0), Nat.cast_sub hkm]
        ring
      rw [habs]
    · intro a ha hna
      positivity
  have hright : ∑ k ∈ Finset.Icc (m + 1) N, (|(k : ℝ) - (m : ℝ)|)⁻¹ ≤
      (harmonic N : ℝ) := by
    have hinj : Set.InjOn (fun k : ℕ => k - m) ↑(Finset.Icc (m + 1) N) := by
      intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have h1 : m ≤ a := by omega
      have h2 : m ≤ b := by omega
      have hab' : a - m = b - m := hab
      calc a = (a - m) + m := (Nat.sub_add_cancel h1).symm
        _ = (b - m) + m := by rw [hab']
        _ = b := Nat.sub_add_cancel h2
    have hmap : Finset.image (fun k : ℕ => k - m) (Finset.Icc (m + 1) N) ⊆
        Finset.Icc 1 N := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    have hmain := Finset.sum_le_sum_of_injOn
      (f := fun k : ℕ => (|(k : ℝ) - (m : ℝ)|)⁻¹)
      (g := fun j : ℕ => ((j : ℝ))⁻¹) (fun k : ℕ => k - m) hinj hmap ?_ ?_
    · calc ∑ k ∈ Finset.Icc (m + 1) N, (|(k : ℝ) - (m : ℝ)|)⁻¹
          ≤ ∑ j ∈ Finset.Icc 1 N, ((j : ℝ))⁻¹ := hmain
        _ = (harmonic N : ℝ) := by
            rw [harmonic_eq_sum_Icc]
            simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hmk : m ≤ k := by omega
      have hkr : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
      have habs : |(k : ℝ) - (m : ℝ)| = ((k - m : ℕ) : ℝ) := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - (m : ℝ)), Nat.cast_sub hmk]
      rw [habs]
    · intro a ha hna
      positivity
  have hsub : Finset.Icc 1 N ⊆ (Finset.Icc 1 (m - 1) ∪ {m}) ∪ Finset.Icc (m + 1) N := by
    intro k hk
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton] at hk ⊢
    rcases lt_trichotomy k m with h | h | h
    · exact Or.inl (Or.inl ⟨hk.1, by omega⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨by omega, hk.2⟩
  have hnn : ∀ k ∈ (Finset.Icc 1 (m - 1) ∪ {m}) ∪ Finset.Icc (m + 1) N,
      k ∉ Finset.Icc 1 N → 0 ≤ (|(k : ℝ) - (m : ℝ)|)⁻¹ := by
    intro k _ _
    positivity
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hd1 : Disjoint (Finset.Icc 1 (m - 1) ∪ {m}) (Finset.Icc (m + 1) N) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at ha hb
    omega
  have hd2 : Disjoint (Finset.Icc 1 (m - 1)) ({m} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc, Finset.mem_singleton] at ha hb
    omega
  rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton] at hmono
  have hfm : (|((m : ℕ) : ℝ) - (m : ℝ)|)⁻¹ = 0 := by simp
  rw [hfm, add_zero] at hmono
  linarith

/-! ### Rescaling the sharp cut error onto the integer distance -/

/-- `log (1 + s) ≥ s/(1+s)` for `s ≥ 0`. -/
private theorem log_one_add_ge {s : ℝ} (hs : 0 ≤ s) :
    s / (1 + s) ≤ Real.log (1 + s) := by
  have hpos : (0 : ℝ) < 1 + s := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h1 : (1 : ℝ) - (1 + s)⁻¹ = s / (1 + s) := by
    field_simp
    ring
  rwa [h1] at h

/-- Distance to the integer part controls the inverse distance to a real cut. -/
private theorem inv_abs_sub_le_inv_abs_sub_floor {u : ℝ} (hu : 0 ≤ u) {k : ℕ}
    (hk : 4 ≤ |(k : ℝ) - u|) :
    (|(k : ℝ) - u|)⁻¹ ≤ (4 / 3 : ℝ) * (|(k : ℝ) - (⌊u⌋₊ : ℝ)|)⁻¹ := by
  have h1 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  have h2 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu
  have hd : |u - (⌊u⌋₊ : ℝ)| < 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have htri : |(k : ℝ) - (⌊u⌋₊ : ℝ)| ≤ |(k : ℝ) - u| + |u - (⌊u⌋₊ : ℝ)| := by
    have he : (k : ℝ) - (⌊u⌋₊ : ℝ) = ((k : ℝ) - u) + (u - (⌊u⌋₊ : ℝ)) := by ring
    calc |(k : ℝ) - (⌊u⌋₊ : ℝ)| = |((k : ℝ) - u) + (u - (⌊u⌋₊ : ℝ))| := by rw [he]
      _ ≤ _ := abs_add_le _ _
  have hA : (0 : ℝ) < |(k : ℝ) - u| := by linarith
  have hB : (0 : ℝ) < |(k : ℝ) - (⌊u⌋₊ : ℝ)| := by
    rcases eq_or_lt_of_le (abs_nonneg ((k : ℝ) - (⌊u⌋₊ : ℝ))) with h | h
    · exfalso
      have htr2 : |(k : ℝ) - u| ≤ |(k : ℝ) - (⌊u⌋₊ : ℝ)| + |(⌊u⌋₊ : ℝ) - u| := by
        have he : (k : ℝ) - u = ((k : ℝ) - (⌊u⌋₊ : ℝ)) + ((⌊u⌋₊ : ℝ) - u) := by ring
        calc |(k : ℝ) - u| = |((k : ℝ) - (⌊u⌋₊ : ℝ)) + ((⌊u⌋₊ : ℝ) - u)| := by rw [he]
          _ ≤ _ := abs_add_le _ _
      rw [← h] at htr2
      have hd' : |(⌊u⌋₊ : ℝ) - u| < 1 := by rw [abs_sub_comm]; exact hd
      linarith
    · exact h
  have hkey : (3 / 4 : ℝ) * |(k : ℝ) - (⌊u⌋₊ : ℝ)| ≤ |(k : ℝ) - u| := by
    nlinarith [htri, hd, hk, hB, hA]
  calc (|(k : ℝ) - u|)⁻¹ ≤ ((3 / 4 : ℝ) * |(k : ℝ) - (⌊u⌋₊ : ℝ)|)⁻¹ :=
        inv_anti₀ (by positivity) hkey
    _ = (4 / 3 : ℝ) * (|(k : ℝ) - (⌊u⌋₊ : ℝ)|)⁻¹ := by
        rw [mul_inv, show ((3:ℝ)/4)⁻¹ = 4/3 by norm_num]

/-- The sharp cut error, rescaled to the integer distance from the cut. -/
private theorem sharp_kernel_rescale {u k T : ℝ} (hu : 0 < u) (hk : 0 < k) (hT : 0 < T)
    (h2 : u / k ≤ 2) (hle4 : |k - u| ≤ 4 * u) (hpos : 0 < |k - u|) :
    (u / k) ^ (1 / 2 : ℝ) / (Real.pi * T * |Real.log (u / k)|)
      ≤ 20 * u / (Real.pi * T * |k - u|) := by
  have hw2 : (u / k) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc (u / k) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h2 (by norm_num)
      _ ≤ 2 := by
          calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hne1 : u / k ≠ 1 := by
    intro h
    have hku : u = k := by
      field_simp at h
      linarith
    rw [hku, sub_self, abs_zero] at hpos
    exact lt_irrefl _ hpos
  have hlogpos : (0 : ℝ) < |Real.log (u / k)| := by
    rw [abs_pos]
    intro h
    apply hne1
    have hq : (0 : ℝ) < u / k := div_pos hu hk
    calc u / k = Real.exp (Real.log (u / k)) := (Real.exp_log hq).symm
      _ = Real.exp 0 := by rw [h]
      _ = 1 := Real.exp_zero
  have hlog : |k - u| / (5 * u) ≤ |Real.log (u / k)| := by
    rcases le_or_gt |k - u| (u / 2) with hnear | hfar
    · have huk : u / k = (1 + (k - u) / u)⁻¹ := by
        have h1 : 1 + (k - u) / u = k / u := by
          field_simp
          ring
        rw [h1, inv_div]
      rw [huk, Real.log_inv, abs_neg]
      have hb := abs_le.mp hnear
      have hs1 : -1 < (k - u) / u := by
        rw [lt_div_iff₀ hu]
        nlinarith [hb.1]
      have hs2 : (k - u) / u ≤ 1 := by
        rw [div_le_iff₀ hu]
        nlinarith [hb.2]
      have hl := log_one_add_abs_lower hs1 hs2
      have habs : |(k - u) / u| = |k - u| / u := by rw [abs_div, abs_of_pos hu]
      rw [habs] at hl
      calc |k - u| / (5 * u) ≤ |k - u| / (2 * u) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            linarith
        _ = |k - u| / u / 2 := by field_simp
        _ ≤ _ := hl
    · have hku : u < k := by
        rcases lt_or_ge u k with h | h
        · exact h
        · have h3 : u ≤ 2 * k := by
            rw [div_le_iff₀ hk] at h2
            linarith
          have h4 : |k - u| = u - k := by
            rw [abs_of_nonpos (by linarith)]
            ring
          rw [h4] at hfar
          linarith
      have hx0 : (0 : ℝ) < (k - u) / u := by
        apply div_pos _ hu
        linarith
      have hs4 : (k - u) / u ≤ 4 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ k - u)] at hle4
        rw [div_le_iff₀ hu]
        linarith
      have huk : u / k = (1 + (k - u) / u)⁻¹ := by
        have h1 : 1 + (k - u) / u = k / u := by
          field_simp
          ring
        rw [h1, inv_div]
      have h1 : |Real.log (u / k)| = Real.log (1 + (k - u) / u) := by
        rw [huk, Real.log_inv, abs_neg,
          abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + (k - u) / u))]
      have h2 : |k - u| = k - u := abs_of_nonneg (by linarith : (0 : ℝ) ≤ k - u)
      have hga := log_one_add_ge hx0.le
      have h2' : (k - u) / u / (1 + (k - u) / u) = (k - u) / k := by
        field_simp
        ring
      rw [h2'] at hga
      have hk5 : k ≤ 5 * u := by
        have h := hle4
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ k - u)] at h
        linarith
      have h3 : (k - u) / (5 * u) ≤ (k - u) / k := by
        apply div_le_div_of_nonneg_left (by linarith) (by positivity)
        linarith
      rw [h1, h2]
      exact le_trans h3 hga
  have hB : (0 : ℝ) < Real.pi * T * (|k - u| / (5 * u)) := by positivity
  calc (u / k) ^ (1 / 2 : ℝ) / (Real.pi * T * |Real.log (u / k)|)
      ≤ 2 / (Real.pi * T * |Real.log (u / k)|) := by gcongr
    _ ≤ 2 / (Real.pi * T * (|k - u| / (5 * u))) := by gcongr
    _ = 10 * u / (Real.pi * T * |k - u|) := by
        have hA : (0 : ℝ) < Real.pi * T := by positivity
        have hB : (0 : ℝ) < |k - u| := hpos
        field_simp
        ring
    _ ≤ 20 * u / (Real.pi * T * |k - u|) := by gcongr; norm_num

/-! ### Summing the cut errors over the polynomial support -/

/-- Splitting a two-branch sum along its predicate. -/
private theorem splitsum_ite {s : Finset ℕ} (p : ℕ → Prop) [DecidablePred p]
    (A : ℝ) (B : ℕ → ℝ) :
    ∑ k ∈ s, (if p k then A else B k)
      = A * ((s.filter p).card : ℝ) + ∑ k ∈ s.filter (fun k => ¬ p k), B k := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := s) (p := p)
    (f := fun k => if p k then A else B k)]
  congr 1
  · rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_filter.mp hk).2)]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  · exact Finset.sum_congr rfl (fun k hk => if_neg (Finset.mem_filter.mp hk).2)

set_option maxHeartbeats 4000000 in
/-- Sum of the cut errors over the polynomial support, for one real cut. -/
private theorem perron_cut_sum_bound
    {u x T M : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ℝ → ℕ → ℝ}
    (hx : 3 ≤ x) (hu1 : x / 2 ≤ u) (hu2 : u ≤ x) (hT4 : 4 ≤ T) (hTu : T ≤ u)
    (hM : 0 ≤ M) (hc : ∀ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) *
        (((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
            (((u / k : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))))
          - (if 1 < u / (k : ℝ) then 1 else 0))‖
      ≤ 110 * M * (x / T) * (1 + Real.log (2 * x)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  set S := Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊ with hS
  set m : ℕ := ⌊u⌋₊ with hm
  have hk1 : ∀ k ∈ S, 1 ≤ k := by
    intro k hk
    have h := (Finset.mem_Ioc.mp hk).1
    omega
  have hkx : ∀ k ∈ S, (k : ℝ) ≤ 2 * x := by
    intro k hk
    have h := (Finset.mem_Ioc.mp hk).2
    have h1 : (k : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) := by exact_mod_cast h
    have h2 : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
    linarith
  have hkl : ∀ k ∈ S, x / 2 < (k : ℝ) := by
    intro k hk
    have h := (Finset.mem_Ioc.mp hk).1
    have h1 : x / 2 < (⌊x / 2⌋₊ : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (x / 2)
      linarith
    have h2 : (⌊x / 2⌋₊ : ℝ) + 1 ≤ (k : ℝ) := by
      have h3 : ⌊x / 2⌋₊ + 1 ≤ k := by omega
      exact_mod_cast h3
    linarith
  have hkpos : ∀ k ∈ S, (0 : ℝ) < (k : ℝ) := fun k hk => by
    have := hk1 k hk
    exact_mod_cast (by omega : 0 < k)
  have hw0 : ∀ k ∈ S, 0 < u / (k : ℝ) := fun k hk => div_pos hu0 (hkpos k hk)
  have hwhi : ∀ k ∈ S, u / (k : ℝ) ≤ 2 := by
    intro k hk
    rw [div_le_iff₀ (hkpos k hk)]
    nlinarith [hkl k hk, hu2]
  have hwlo : ∀ k ∈ S, 1 / 4 ≤ u / (k : ℝ) := by
    intro k hk
    rw [le_div_iff₀ (hkpos k hk)]
    nlinarith [hkx k hk, hu1]
  have hm1 : 1 ≤ m := by
    rw [hm]
    apply Nat.le_floor
    show ((1 : ℕ) : ℝ) ≤ u
    push_cast
    linarith
  have hmN : m ≤ ⌊2 * x⌋₊ := by
    rw [hm]
    exact Nat.floor_mono (by linarith)
  -- per-term bound
  set P : ℕ → Prop := fun k => |(k : ℝ) - u| ≤ 4 * u / T with hP
  have hterm : ∀ k ∈ S, ‖(a x k : ℂ) * χ (k : ZMod q) *
      (((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
          (((u / k : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))))
        - (if 1 < u / (k : ℝ) then 1 else 0))‖
      ≤ M * (if P k then 9 * (1 + Real.log T) else 20 * u / (Real.pi * T * |(k : ℝ) - u|)) := by
    intro k hk
    rw [norm_mul]
    refine mul_le_mul (hc k hk) ?_ (norm_nonneg _) hM
    by_cases hcs : P k
    · rw [if_pos hcs]
      exact perron_err_crude (hwlo k hk) (hwhi k hk) (by linarith : (1 : ℝ) ≤ T)
    · rw [if_neg hcs]
      have hcs' : ¬ |(k : ℝ) - u| ≤ 4 * u / T := hcs
      have hlt : 4 * u / T < |(k : ℝ) - u| := lt_of_not_ge hcs'
      have hpos : (0 : ℝ) < |(k : ℝ) - u| := by
        have h1 : (0 : ℝ) < 4 * u / T := by positivity
        linarith
      have hle4 : |(k : ℝ) - u| ≤ 4 * u := by
        have h3 := hkx k hk
        have h4 := hkl k hk
        rw [abs_le]
        constructor <;> linarith
      have hne : u / (k : ℝ) ≠ 1 := by
        intro h
        have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (hkpos k hk)
        have hku : u = (k : ℝ) := (div_eq_one_iff_eq hk0).mp h
        rw [← hku, sub_self, abs_zero] at hpos
        exact lt_irrefl _ hpos
      have hsharp := perron_kernel_half (hw0 k hk) hne hT0
      have hres := sharp_kernel_rescale hu0 (hkpos k hk) hT0 (hwhi k hk) hle4 hpos
      exact hsharp.trans hres
  -- the saturated and far parts
  set NF : Finset ℕ := S.filter P with hNF
  set FF : Finset ℕ := S.filter (fun k => ¬ P k) with hFF
  have hcard : ((NF).card : ℝ) ≤ 8 * u / T + 2 := by
    have hA0 : (0 : ℝ) ≤ u - 4 * u / T := by
      have h1 : 4 * u / T ≤ u := by
        rw [div_le_iff₀ hT0]
        nlinarith [hTu]
      linarith
    have hAB : u - 4 * u / T ≤ u + 4 * u / T := by
      have h0 : (0 : ℝ) ≤ 4 * u / T := by positivity
      linarith
    have hmem : ∀ k ∈ NF, (u - 4 * u / T) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (u + 4 * u / T) := by
      intro k hk
      have hkP : P k := by
        rw [hNF] at hk
        exact (Finset.mem_filter.mp hk).2
      have hb := abs_le.mp hkP
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have h := card_le_of_forall_mem_Icc (A := u - 4 * u / T) (B := u + 4 * u / T)
      (s := NF) hA0 hAB hmem
    have h2 : (u + 4 * u / T) - (u - 4 * u / T) + 2 = 8 * u / T + 2 := by ring
    linarith [h, h2]
  have hsubS : S ⊆ Finset.Icc 1 ⌊2 * x⌋₊ := fun k hk =>
    Finset.mem_Icc.mpr ⟨hk1 k hk, (Finset.mem_Ioc.mp hk).2⟩
  have hmom : (∑ k ∈ FF, (|(k : ℝ) - (m : ℝ)|)⁻¹) ≤ 2 * (1 + Real.log (2 * x)) := by
    have hsub : FF ⊆ S := by
      rw [hFF]
      exact Finset.filter_subset _ _
    calc (∑ k ∈ FF, (|(k : ℝ) - (m : ℝ)|)⁻¹)
        ≤ ∑ k ∈ S, (|(k : ℝ) - (m : ℝ)|)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
      _ ≤ ∑ k ∈ Finset.Icc 1 ⌊2 * x⌋₊, (|(k : ℝ) - (m : ℝ)|)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubS (fun k _ _ => by positivity)
      _ ≤ 2 * (harmonic ⌊2 * x⌋₊ : ℝ) := sum_inv_abs_sub_le _ _ hm1 hmN
      _ ≤ 2 * (1 + Real.log (2 * x)) := by
          have h3 : (harmonic ⌊2 * x⌋₊ : ℝ) ≤ 1 + Real.log (2 * x) := by
            refine (harmonic_le_one_add_log ⌊2 * x⌋₊).trans ?_
            have h4 : (0 : ℝ) < (⌊2 * x⌋₊ : ℝ) := by
              have h5 : 1 ≤ ⌊2 * x⌋₊ := by
                apply Nat.le_floor
                show ((1 : ℕ) : ℝ) ≤ 2 * x
                push_cast
                linarith
              exact_mod_cast (by omega : 0 < ⌊2 * x⌋₊)
            have h5 := Real.log_le_log h4 (Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * x))
            linarith
          linarith
  have hfar : ∑ k ∈ FF, 20 * u / (Real.pi * T * |(k : ℝ) - u|)
      ≤ (20 * u / (Real.pi * T)) * (4 / 3) * (2 * (1 + Real.log (2 * x))) := by
    have hstep : ∑ k ∈ FF, 20 * u / (Real.pi * T * |(k : ℝ) - u|)
        ≤ (20 * u / (Real.pi * T)) * ∑ k ∈ FF, (4 / 3 : ℝ) * (|(k : ℝ) - (m : ℝ)|)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hknP : ¬ P k := by
        rw [hFF] at hk
        exact (Finset.mem_filter.mp hk).2
      have h4 : 4 ≤ |(k : ℝ) - u| := by
        have h1 : 4 ≤ 4 * u / T := by
          rw [le_div_iff₀ hT0]
          nlinarith [hTu]
        have h2 := lt_of_not_ge hknP
        linarith
      have hinv : (|(k : ℝ) - u|)⁻¹ ≤ (4 / 3 : ℝ) * (|(k : ℝ) - (m : ℝ)|)⁻¹ :=
        inv_abs_sub_le_inv_abs_sub_floor hu0.le h4
      have hp : (0 : ℝ) < |(k : ℝ) - u| := by linarith
      have hA : (0 : ℝ) < Real.pi * T := by positivity
      have heq : 20 * u / (Real.pi * T * |(k : ℝ) - u|)
          = (20 * u / (Real.pi * T)) * (|(k : ℝ) - u|)⁻¹ := by
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    calc ∑ k ∈ FF, 20 * u / (Real.pi * T * |(k : ℝ) - u|)
        ≤ (20 * u / (Real.pi * T)) * ∑ k ∈ FF, (4 / 3 : ℝ) * (|(k : ℝ) - (m : ℝ)|)⁻¹ := hstep
      _ = (20 * u / (Real.pi * T)) * ((4 / 3 : ℝ) * ∑ k ∈ FF, (|(k : ℝ) - (m : ℝ)|)⁻¹) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (20 * u / (Real.pi * T)) * ((4 / 3 : ℝ) * (2 * (1 + Real.log (2 * x)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmom (by norm_num))
            (by positivity)
      _ = (20 * u / (Real.pi * T)) * (4 / 3) * (2 * (1 + Real.log (2 * x))) := by ring
  -- the numerical combination
  have hL' : (0 : ℝ) ≤ 1 + Real.log (2 * x) := by
    have h1 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    linarith
  have hxT : 1 ≤ x / T := by
    rw [le_div_iff₀ hT0]
    linarith
  have hA2 : 8 * u / T + 2 ≤ 10 * (x / T) := by
    have hx1 : 8 * u / T ≤ 8 * (x / T) := by
      have e : 8 * (x / T) = 8 * x / T := by ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hT0.le
      linarith
    have h3 : 2 ≤ 2 * (x / T) := by linarith
    have hg : 10 * (x / T) = 8 * (x / T) + 2 * (x / T) := by ring
    rw [hg]
    linarith
  have hB2 : 9 * (1 + Real.log T) * (8 * u / T + 2)
      ≤ 90 * (x / T) * (1 + Real.log (2 * x)) := by
    have h1 : (0 : ℝ) ≤ 9 * (1 + Real.log (2 * x)) := by linarith
    have h2 : 9 * (1 + Real.log T) ≤ 9 * (1 + Real.log (2 * x)) := by
      have h3 : Real.log T ≤ Real.log (2 * x) := Real.log_le_log hT0 (by linarith)
      linarith
    calc 9 * (1 + Real.log T) * (8 * u / T + 2)
        ≤ 9 * (1 + Real.log (2 * x)) * (10 * (x / T)) :=
          mul_le_mul h2 hA2 (by linarith) h1
      _ = 90 * (x / T) * (1 + Real.log (2 * x)) := by ring
  have hC2 : (20 * u / (Real.pi * T)) * (4 / 3) * (2 * (1 + Real.log (2 * x)))
      ≤ 20 * (x / T) * (1 + Real.log (2 * x)) := by
    have h4 : (20 * u / (Real.pi * T)) * (4 / 3) * (2 * (1 + Real.log (2 * x)))
        = (160 / (3 * Real.pi)) * (u / T) * (1 + Real.log (2 * x)) := by
      field_simp
      ring
    rw [h4]
    have h5 : (160 / (3 * Real.pi)) ≤ 20 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    have h6 : u / T ≤ x / T := div_le_div_of_nonneg_right hu2 hT0.le
    have h7 : (0 : ℝ) ≤ (u / T) * (1 + Real.log (2 * x)) := by positivity
    calc (160 / (3 * Real.pi)) * (u / T) * (1 + Real.log (2 * x))
        = (160 / (3 * Real.pi)) * ((u / T) * (1 + Real.log (2 * x))) := by ring
      _ ≤ 20 * ((u / T) * (1 + Real.log (2 * x))) := mul_le_mul_of_nonneg_right h5 h7
      _ ≤ 20 * ((x / T) * (1 + Real.log (2 * x))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right h6 hL'
      _ = 20 * (x / T) * (1 + Real.log (2 * x)) := by ring
  have hsplit : ∑ k ∈ S, (if P k then (9 * (1 + Real.log T)) else
        20 * u / (Real.pi * T * |(k : ℝ) - u|))
      = 9 * (1 + Real.log T) * ((NF).card : ℝ) + ∑ k ∈ FF,
          20 * u / (Real.pi * T * |(k : ℝ) - u|) := by
    rw [splitsum_ite (p := P) (A := 9 * (1 + Real.log T))
      (B := fun k => 20 * u / (Real.pi * T * |(k : ℝ) - u|))]
  -- assembly
  calc ‖∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) *
        (((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
            (((u / k : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))))
          - (if 1 < u / (k : ℝ) then 1 else 0))‖
      ≤ ∑ k ∈ S, ‖(a x k : ℂ) * χ (k : ZMod q) *
        (((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
            (((u / k : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))))
          - (if 1 < u / (k : ℝ) then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S, M * (if P k then 9 * (1 + Real.log T)
          else 20 * u / (Real.pi * T * |(k : ℝ) - u|)) := Finset.sum_le_sum hterm
    _ = M * (9 * (1 + Real.log T) * ((NF).card : ℝ) + ∑ k ∈ FF,
          20 * u / (Real.pi * T * |(k : ℝ) - u|)) := by
        rw [← Finset.mul_sum, hsplit]
    _ ≤ M * (9 * (1 + Real.log T) * (8 * u / T + 2)
          + (20 * u / (Real.pi * T)) * (4 / 3) * (2 * (1 + Real.log (2 * x)))) := by
        apply mul_le_mul_of_nonneg_left _ hM
        have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
        exact add_le_add (mul_le_mul_of_nonneg_left hcard (by positivity)) hfar
    _ ≤ 110 * M * (x / T) * (1 + Real.log (2 * x)) := by
        have h12 : 9 * (1 + Real.log T) * (8 * u / T + 2)
            + (20 * u / (Real.pi * T)) * (4 / 3) * (2 * (1 + Real.log (2 * x)))
            ≤ 110 * (x / T) * (1 + Real.log (2 * x)) := by
          have hh := add_le_add hB2 hC2
          nlinarith [hh]
        calc M * (9 * (1 + Real.log T) * (8 * u / T + 2)
              + (20 * u / (Real.pi * T)) * (4 / 3) * (2 * (1 + Real.log (2 * x))))
            ≤ M * (110 * (x / T) * (1 + Real.log (2 * x))) :=
              mul_le_mul_of_nonneg_left h12 hM
          _ = 110 * M * (x / T) * (1 + Real.log (2 * x)) := by ring

/-! ### Indicator bookkeeping for the Perron window -/

/-- A sum of a `0/1` indicator over at most one point is at most one. -/
private theorem sum_indicator_le_one {s : Finset ℕ} {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ a ∈ s, ∀ b ∈ s, p a → p b → a = b) :
    ∑ k ∈ s, (if p k then (1 : ℝ) else 0) ≤ 1 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : s.filter p ⊆ s := Finset.filter_subset _ _
  have h2 : (s.filter p).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact hp a (h1 ha) b (h1 hb) (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast h2

/-- The equality part of an indicator over the integers is at most one. -/
private theorem eq_indicator_sum_le_one {s : Finset ℕ} {u : ℝ} :
    ∑ k ∈ s, ((if (k : ℝ) ≤ u then (1 : ℝ) else 0) - (if (k : ℝ) < u then (1 : ℝ) else 0))
      ≤ 1 := by
  have hpt : ∀ k : ℕ,
      ((if (k : ℝ) ≤ u then (1 : ℝ) else 0) - (if (k : ℝ) < u then (1 : ℝ) else 0))
        = (if ((k : ℝ) ≤ u ∧ ¬ (k : ℝ) < u) then (1 : ℝ) else 0) := by
    intro k
    by_cases h1 : (k : ℝ) ≤ u
    · by_cases h2 : (k : ℝ) < u
      · rw [if_pos h1, if_pos h2, if_neg (by tauto)]
        ring
      · rw [if_pos h1, if_neg h2, if_pos ⟨h1, h2⟩]
        ring
    · rw [if_neg h1, if_neg (by linarith : ¬ (k : ℝ) < u), if_neg (by tauto)]
      ring
  rw [Finset.sum_congr rfl (fun k _ => hpt k)]
  apply sum_indicator_le_one
  intro a ha b hb ha' hb'
  have h1 : (a : ℝ) = u := le_antisymm ha'.1 (not_lt.mp ha'.2)
  have h2 : (b : ℝ) = u := le_antisymm hb'.1 (not_lt.mp hb'.2)
  exact_mod_cast h1.trans h2.symm

/-- The strict comparison with a positive cut is a Perron step. -/
private theorem indicator_lt_div {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : 1 ≤ k) :
    (if (k : ℝ) < u then (1 : ℂ) else 0) = (if 1 < u / (k : ℝ) then (1 : ℂ) else 0) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  by_cases h : (k : ℝ) < u
  · have h2 : 1 < u / (k : ℝ) := by
      rw [lt_div_iff₀ hkpos]
      linarith
    rw [if_pos h, if_pos h2]
  · have h2 : ¬ (1 < u / (k : ℝ)) := by
      rw [lt_div_iff₀ hkpos]
      linarith
    rw [if_neg h, if_neg h2]

/-- The equality part of the indicator contributes at most one bound. -/
private theorem eq_term_bound {S : Finset ℕ} {c : ℕ → ℂ} {M : ℝ} (u : ℝ)
    (hM : 0 ≤ M) (hc : ∀ k ∈ S, ‖c k‖ ≤ M) :
    ‖∑ k ∈ S, c k * ((if (k : ℝ) ≤ u then (1 : ℂ) else 0)
      - (if (k : ℝ) < u then (1 : ℂ) else 0))‖ ≤ M := by
  have h1 : ∀ k ∈ S, ‖c k * ((if (k : ℝ) ≤ u then (1 : ℂ) else 0)
      - (if (k : ℝ) < u then (1 : ℂ) else 0))‖
      ≤ M * ((if (k : ℝ) ≤ u then (1 : ℝ) else 0) - (if (k : ℝ) < u then (1 : ℝ) else 0)) := by
    intro k hk
    have hE : (0 : ℝ) ≤ (if (k : ℝ) ≤ u then (1 : ℝ) else 0)
        - (if (k : ℝ) < u then (1 : ℝ) else 0) := by
      by_cases h1 : (k : ℝ) ≤ u
      · by_cases h2 : (k : ℝ) < u
        · simp only [if_pos h1, if_pos h2]; norm_num
        · simp only [if_pos h1, if_neg h2]; norm_num
      · simp only [if_neg h1, if_neg (by linarith : ¬ (k : ℝ) < u)]
        norm_num
    have hnorm : ‖(if (k : ℝ) ≤ u then (1 : ℂ) else 0)
        - (if (k : ℝ) < u then (1 : ℂ) else 0)‖
        = ((if (k : ℝ) ≤ u then (1 : ℝ) else 0) - (if (k : ℝ) < u then (1 : ℝ) else 0)) := by
      by_cases h1 : (k : ℝ) ≤ u
      · by_cases h2 : (k : ℝ) < u
        · simp only [if_pos h1, if_pos h2, sub_self, norm_zero]
        · simp only [if_pos h1, if_neg h2, sub_zero, Complex.norm_real, Real.norm_eq_abs,
            abs_one, Complex.ofReal_one]
          norm_num
      · simp only [if_neg h1, if_neg (by linarith : ¬ (k : ℝ) < u), sub_zero, norm_zero]
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_right (hc k hk) hE
  calc ‖∑ k ∈ S, c k * ((if (k : ℝ) ≤ u then (1 : ℂ) else 0)
        - (if (k : ℝ) < u then (1 : ℂ) else 0))‖
      ≤ ∑ k ∈ S, ‖c k * ((if (k : ℝ) ≤ u then (1 : ℂ) else 0)
        - (if (k : ℝ) < u then (1 : ℂ) else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S, M * ((if (k : ℝ) ≤ u then (1 : ℝ) else 0)
        - (if (k : ℝ) < u then (1 : ℝ) else 0)) := Finset.sum_le_sum h1
    _ = M * ∑ k ∈ S, ((if (k : ℝ) ≤ u then (1 : ℝ) else 0)
        - (if (k : ℝ) < u then (1 : ℝ) else 0)) := by rw [Finset.mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left eq_indicator_sum_le_one hM
    _ = M := mul_one M

set_option maxHeartbeats 2000000 in
/-- The leaf's partial sum, written as an indicator sum over the polynomial support. -/
private theorem sum_range_convert {x y : ℝ} (hx : 3 ≤ x) (hy0 : 0 < y) (hyw : y ≤ x / 2)
    (a : ℝ → ℕ → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q))
      = ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) *
          ((if (k : ℝ) ≤ x then (1 : ℂ) else 0) - (if (k : ℝ) ≤ x - y then (1 : ℂ) else 0)) := by
  have hTS : Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ ⊆ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊ := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hk
    have h3 : ⌊x / 2⌋₊ ≤ ⌊x - y⌋₊ := Nat.floor_mono (by linarith)
    have h4 : ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := Nat.floor_mono (by linarith)
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have h1 : ∀ k : ℕ, ((k : ℝ) ≤ x) ↔ k ≤ ⌊x⌋₊ := by
    intro k
    constructor
    · intro h; exact Nat.le_floor h
    · intro h
      exact (by exact_mod_cast h : (k : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
  have h2 : ∀ k : ℕ, ((k : ℝ) ≤ x - y) ↔ k ≤ ⌊x - y⌋₊ := by
    intro k
    constructor
    · intro h; exact Nat.le_floor h
    · intro h
      exact (by exact_mod_cast h : (k : ℝ) ≤ (⌊x - y⌋₊ : ℝ)).trans
        (Nat.floor_le (by linarith))
  have hpt : ∀ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (a x k : ℂ) * χ (k : ZMod q) *
        ((if (k : ℝ) ≤ x then (1 : ℂ) else 0) - (if (k : ℝ) ≤ x - y then (1 : ℂ) else 0))
      = (if k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ then (a x k : ℂ) * χ (k : ZMod q) else 0) := by
    intro k hk
    have h3 : (if (k : ℝ) ≤ x then (1 : ℂ) else 0) = (if k ≤ ⌊x⌋₊ then (1 : ℂ) else 0) :=
      if_congr (h1 k) rfl rfl
    have h4 : (if (k : ℝ) ≤ x - y then (1 : ℂ) else 0)
        = (if k ≤ ⌊x - y⌋₊ then (1 : ℂ) else 0) := if_congr (h2 k) rfl rfl
    rw [h3, h4]
    by_cases hA : k ≤ ⌊x - y⌋₊
    · have hB : k ≤ ⌊x⌋₊ := by
        have h5 : ⌊x - y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
        omega
      have hnot : ¬ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ := by
        simp only [Finset.mem_Ioc]
        omega
      rw [if_pos hB, if_pos hA, if_neg hnot]
      ring
    · have hA' : ⌊x - y⌋₊ < k := by omega
      by_cases hB : k ≤ ⌊x⌋₊
      · have hmem : k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ := Finset.mem_Ioc.mpr ⟨hA', hB⟩
        rw [if_pos hB, if_neg hA, if_pos hmem]
        ring
      · have hnot : ¬ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ := by
          simp only [Finset.mem_Ioc]
          omega
        rw [if_neg hB, if_neg hA, if_neg hnot]
        ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTS]

set_option maxHeartbeats 4000000 in
/-- Error of one cut against the indicator sum over the polynomial support. -/
private theorem cut_error_bound {u x T M : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    {a : ℝ → ℕ → ℝ} {J : ℕ → ℂ}
    (hJ : ∀ k : ℕ, J k = (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, ((((u / k : ℝ) : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))))
    (hx : 3 ≤ x) (hu1 : x / 2 ≤ u) (hu2 : u ≤ x) (hT4 : 4 ≤ T) (hTu : T ≤ u) (hu0 : 0 < u)
    (hM : 0 ≤ M) (hc : ∀ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ u then (1 : ℂ) else 0)) - J k)‖
      ≤ 110 * M * (x / T) * (1 + Real.log (2 * x)) + M := by
  set S := Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊ with hS
  have hk1 : ∀ k ∈ S, 1 ≤ k := by
    intro k hk
    have h := (Finset.mem_Ioc.mp hk).1
    omega
  have hsum : (∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ u then (1 : ℂ) else 0)) - J k))
      = (∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) < u then (1 : ℂ) else 0)) - J k))
        + ∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ u then (1 : ℂ) else 0)) - ((if (k : ℝ) < u then (1 : ℂ) else 0))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hstrict : (∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) < u then (1 : ℂ) else 0)) - J k))
      = ∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * (((if 1 < u / (k : ℝ) then (1 : ℂ) else 0)) - J k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [indicator_lt_div hu0 (hk1 k hk)]
  have hmain : ‖∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, ((((u / k : ℝ) : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))) - ((if 1 < u / (k : ℝ) then (1 : ℂ) else 0)))‖
      ≤ 110 * M * (x / T) * (1 + Real.log (2 * x)) :=
    perron_cut_sum_bound χ hx hu1 hu2 hT4 hTu hM hc
  have hneg : (∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * (((if 1 < u / (k : ℝ) then (1 : ℂ) else 0)) - J k))
      = -(∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, ((((u / k : ℝ) : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))) - ((if 1 < u / (k : ℝ) then (1 : ℂ) else 0)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hJ k]
    ring
  have hmain2 : ‖∑ k ∈ S, (a x k : ℂ) * χ (k : ZMod q) * (((if 1 < u / (k : ℝ) then (1 : ℂ) else 0)) - J k)‖
      ≤ 110 * M * (x / T) * (1 + Real.log (2 * x)) := by
    rw [hneg, norm_neg]
    exact hmain
  rw [hsum, hstrict]
  exact (norm_add_le _ _).trans (add_le_add hmain2 (eq_term_bound u hM hc))


/-- LEAF. Page 25, display 4.3, with the stated heights from page 24.
Only sharp Perron truncation and its coefficient error are required.
No mean value or reference average is used. -/
private theorem truncated_perron_window (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
        ‖(∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
          windowContour a x y (x ^ (0.45 - 2 * ε / 3)) χ‖ ≤
            C * x ^ (0.55 + 11 * ε / 12) := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  intro ε hε hε10 a ha
  have hε8 : (0 : ℝ) < ε / 8 := by linarith
  have hα : (0 : ℝ) < 0.45 - 2 * ε / 3 := by linarith
  have hβ : (0 : ℝ) < 1 - (0.45 - 2 * ε / 3) := by linarith
  obtain ⟨C₀, hC₀⟩ := ha
  obtain ⟨K, hK, hKb⟩ := coeff_small_power_any B (ε / 8) hε8
  have hb : Thm4.CoeffBound (fun n : ℕ => if n = 0 then 0 else ((n.divisors.card : ℝ) ^ B : ℝ)) B := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [if_true, norm_zero]
      positivity
    · simp only [hn, if_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (n.divisors.card)) _)]
      exact le_rfl
  have hbval : ∀ n : ℕ, 1 ≤ n →
      ((fun m : ℕ => if m = 0 then 0 else ((m.divisors.card : ℝ) ^ B : ℝ)) n)
        = ((n.divisors.card : ℝ) ^ B : ℝ) := by
    intro n hn
    simp only [show n ≠ 0 from by omega, if_false]
  set D : ℝ := |C₀| * K * (2 : ℝ) ^ (ε / 8) with hDdef
  have hD0 : (0 : ℝ) ≤ D := by rw [hDdef]; positivity
  have hD : ∀ (x : ℝ), 0 < x → ∀ (q : ℕ), ∀ χ : DirichletCharacter ℂ q, ∀ k : ℕ,
      1 ≤ k → (k : ℝ) ≤ 2 * x → ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ D * x ^ (ε / 8) := by
    intro x hx0 q χ k hk1 hkx
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hdiv : (k.divisors.card : ℝ) ^ B ≤ K * (k : ℝ) ^ (ε / 8) := by
      have h := hKb _ hb k hk1
      beta_reduce at h
      rw [if_neg (by omega : ¬ k = 0)] at h
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (k.divisors.card)) _)] using h
    have h1 : ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ |a x k| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)
    have h4 : |a x k| ≤ |C₀| * (K * (k : ℝ) ^ (ε / 8)) := by
      have h2 : |a x k| ≤ C₀ * (k.divisors.card : ℝ) ^ B := hC₀ x k
      have h3 : |a x k| ≤ |C₀| * (k.divisors.card : ℝ) ^ B :=
        h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) (by positivity))
      exact h3.trans (mul_le_mul_of_nonneg_left hdiv (abs_nonneg C₀))
    have h5 : (k : ℝ) ^ (ε / 8) ≤ (2 * x) ^ (ε / 8) :=
      Real.rpow_le_rpow hkpos.le hkx (by positivity)
    have h6 : |C₀| * (K * (k : ℝ) ^ (ε / 8)) ≤ D * x ^ (ε / 8) := by
      have h7 : |C₀| * (K * (k : ℝ) ^ (ε / 8)) ≤ |C₀| * (K * (2 * x) ^ (ε / 8)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hK.le) (abs_nonneg C₀)
      have h8 : |C₀| * (K * (2 * x) ^ (ε / 8)) = D * x ^ (ε / 8) := by
        rw [hDdef, Real.mul_rpow (by norm_num) hx0.le]
        ring
      linarith [h7, h8.le, h8.ge]
    exact h1.trans (h4.trans h6)
  have hev1 : ∀ᶠ x : ℝ in Filter.atTop, (4 : ℝ) ≤ (x ^ (0.45 - 2 * ε / 3)) :=
    (tendsto_rpow_atTop hα).eventually (Filter.eventually_ge_atTop 4)
  have hev2 : ∀ᶠ x : ℝ in Filter.atTop, (x ^ (0.45 - 2 * ε / 3)) ≤ x / 2 := by
    have h1 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (1 - (0.45 - 2 * ε / 3)) :=
      (tendsto_rpow_atTop hβ).eventually (Filter.eventually_ge_atTop 2)
    filter_upwards [h1, Filter.eventually_ge_atTop (1 : ℝ)] with x hx1 hx2
    have hx0 : (0 : ℝ) < x := by linarith
    have h2 : (x ^ (0.45 - 2 * ε / 3)) * x ^ (1 - (0.45 - 2 * ε / 3)) = x := by
      rw [← Real.rpow_add hx0,
        show 0.45 - 2 * ε / 3 + (1 - (0.45 - 2 * ε / 3)) = 1 by ring, Real.rpow_one]
    have h3 : (0 : ℝ) < (x ^ (0.45 - 2 * ε / 3)) := Real.rpow_pos_of_pos hx0 _
    nlinarith [h2, hx1]
  have hev3 : ∀ᶠ x : ℝ in Filter.atTop, (1 + Real.log (2 * x)) ≤ x ^ (ε / 8) := by
    have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ (1 : ℝ) ≤ x ^ (ε / 8) / 2 := by
      have hL := (isLittleO_log_rpow_rpow_atTop 1 hε8).def (by norm_num : (0 : ℝ) < 1 / 2)
      filter_upwards [hL, Filter.eventually_ge_atTop (1 : ℝ)] with x hx1 hx2
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx2) _),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx1
      calc Real.log x ^ (1 : ℝ) ≤ 1 / 2 * x ^ (ε / 8) := hx1
        _ = x ^ (ε / 8) / 2 := by ring
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, 2 * (1 + Real.log 2) ≤ x ^ (ε / 8) :=
      (tendsto_rpow_atTop hε8).eventually (Filter.eventually_ge_atTop (2 * (1 + Real.log 2)))
    filter_upwards [h1, h2, Filter.eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx3
    have hx0 : (0 : ℝ) < x := by linarith
    have hlog : Real.log (2 * x) = Real.log 2 + Real.log x :=
      Real.log_mul (by norm_num) (by linarith)
    rw [Real.rpow_one] at hx1
    rw [hlog]
    nlinarith [hx1, hx2]
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    (hev1.and (hev2.and (hev3.and (Filter.eventually_ge_atTop (3 : ℝ)))))
  refine ⟨240 * D, X, ?_⟩
  intro x hx q hq χ y hy hyw
  obtain ⟨hT4, hTx, hlogx, hx3⟩ := hX x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hyx2 : y ≤ x / 2 := hyw.trans (referenceWidth_lt_half_x hx3).le
  have hxy : (0 : ℝ) < x - y := by linarith
  have hT0 : (0 : ℝ) < (x ^ (0.45 - 2 * ε / 3)) := Real.rpow_pos_of_pos hx0 _
  have hL' : (0 : ℝ) ≤ (1 + Real.log (2 * x)) := by
    have h1 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    linarith
  have hM0 : (0 : ℝ) ≤ D * x ^ (ε / 8) := mul_nonneg hD0 (Real.rpow_nonneg hx0.le _)
  have hc : ∀ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ D * x ^ (ε / 8) := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    have hk1 : 1 ≤ k := by omega
    have hkx2 : (k : ℝ) ≤ 2 * x := by
      have h1 : (k : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) := by exact_mod_cast hku
      exact h1.trans (Nat.floor_le (by linarith))
    exact hD x (by linarith) q χ k hk1 hkx2
  set Jx : ℕ → ℂ := fun k => (1 / (2 * Real.pi) : ℂ) * (∫ t in (-(x ^ (0.45 - 2 * ε / 3)))..(x ^ (0.45 - 2 * ε / 3)), ((((x / k : ℝ) : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))) with hJxdef
  set Jv : ℕ → ℂ := fun k => (1 / (2 * Real.pi) : ℂ) * (∫ t in (-(x ^ (0.45 - 2 * ε / 3)))..(x ^ (0.45 - 2 * ε / 3)), (((((x - y) / k : ℝ) : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I))) with hJvdef
  have hxcut := cut_error_bound (u := x) (T := (x ^ (0.45 - 2 * ε / 3))) (M := D * x ^ (ε / 8)) (J := Jx) χ
    (by intro k; simp only [hJxdef]) hx3 (by linarith) le_rfl hT4 (by linarith) hx0 hM0 hc
  have hvcut := cut_error_bound (u := x - y) (T := (x ^ (0.45 - 2 * ε / 3))) (M := D * x ^ (ε / 8)) (J := Jv) χ
    (by intro k; simp only [hJvdef]) hx3 (by linarith) (by linarith) hT4 (by linarith) hxy hM0 hc
  have hconv := sum_range_convert (x := x) (y := y) (q := q) hx3 hy0 hyx2 a χ
  have hwin := windowContour_eq_sum (a := a) (x := x) (y := y) (T := (x ^ (0.45 - 2 * ε / 3)))
    (q := q) χ hx0 hxy
  have hhalf : ∀ t : ℝ, Thm4.half t = (((1 / 2 : ℝ) : ℂ) + t * I) := by
    intro t
    unfold Thm4.half
    push_cast
    ring
  have hTx2 : x / (x ^ (0.45 - 2 * ε / 3)) = x ^ (0.55 + 2 * ε / 3) := by
    rw [div_eq_iff (ne_of_gt hT0)]
    have h2 : x ^ (0.55 + 2 * ε / 3) * (x ^ (0.45 - 2 * ε / 3))
        = x ^ ((0.55 + 2 * ε / 3) + (0.45 - 2 * ε / 3)) := (Real.rpow_add hx0 _ _).symm
    rw [h2, show (0.55 + 2 * ε / 3) + (0.45 - 2 * ε / 3) = 1 by ring, Real.rpow_one]
  have hcomb : x ^ (ε / 8) * x ^ (0.55 + 2 * ε / 3) * x ^ (ε / 8) = x ^ (0.55 + 11 * ε / 12) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hpow : x ^ (ε / 8) ≤ x ^ (0.55 + 11 * ε / 12) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) (by linarith)
  have ha1 : 110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x))
      ≤ 110 * D * x ^ (0.55 + 11 * ε / 12) := by
    rw [hTx2]
    have h1 : 110 * (D * x ^ (ε / 8)) * x ^ (0.55 + 2 * ε / 3) * (1 + Real.log (2 * x))
        ≤ 110 * (D * x ^ (ε / 8)) * x ^ (0.55 + 2 * ε / 3) * x ^ (ε / 8) := by
      apply mul_le_mul_of_nonneg_left hlogx
      positivity
    have h2 : 110 * (D * x ^ (ε / 8)) * x ^ (0.55 + 2 * ε / 3) * x ^ (ε / 8)
        = 110 * D * x ^ (0.55 + 11 * ε / 12) := by
      rw [show 110 * (D * x ^ (ε / 8)) * x ^ (0.55 + 2 * ε / 3) * x ^ (ε / 8)
          = 110 * D * (x ^ (ε / 8) * x ^ (0.55 + 2 * ε / 3) * x ^ (ε / 8)) by ring]
      rw [hcomb]
    linarith [h1, h2]
  have ha2 : 110 * (D * x ^ (ε / 8)) * ((x - y) / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x))
      ≤ 110 * D * x ^ (0.55 + 11 * ε / 12) := by
    have hle : (x - y) / (x ^ (0.45 - 2 * ε / 3)) ≤ x / (x ^ (0.45 - 2 * ε / 3)) :=
      div_le_div_of_nonneg_right (by linarith) hT0.le
    calc 110 * (D * x ^ (ε / 8)) * ((x - y) / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x))
        ≤ 110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x)) := by
          apply mul_le_mul_of_nonneg_right _ hL'
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ 110 * D * x ^ (0.55 + 11 * ε / 12) := ha1
  have harr : (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ x then (1 : ℂ) else 0)) - ((if (k : ℝ) ≤ x - y then (1 : ℂ) else 0))))
        - (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (Jx k - Jv k))
      = (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ x then (1 : ℂ) else 0)) - Jx k))
        - (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ x - y then (1 : ℂ) else 0)) - Jv k)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hfin : (110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x)) + D * x ^ (ε / 8))
      + (110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x)) + D * x ^ (ε / 8))
      ≤ 240 * D * x ^ (0.55 + 11 * ε / 12) := by
    have h1 : 110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x))
        + 110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x))
        ≤ 220 * D * x ^ (0.55 + 11 * ε / 12) := by linarith [ha1]
    have h2 : D * x ^ (ε / 8) + D * x ^ (ε / 8) ≤ 2 * D * x ^ (0.55 + 11 * ε / 12) := by
      have h3 : D * x ^ (ε / 8) ≤ D * x ^ (0.55 + 11 * ε / 12) := mul_le_mul_of_nonneg_left hpow hD0
      linarith
    have hpos : (0 : ℝ) ≤ 240 * D * x ^ (0.55 + 11 * ε / 12) := by positivity
    linarith [h1, h2]
  have hkey : ‖(∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ x then (1 : ℂ) else 0)) - ((if (k : ℝ) ≤ x - y then (1 : ℂ) else 0))))
        - (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (Jx k - Jv k))‖
      ≤ 240 * D * x ^ (0.55 + 11 * ε / 12) := by
    rw [harr]
    refine (norm_sub_le _ _).trans ?_
    calc ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ x then (1 : ℂ) else 0)) - Jx k)‖
          + ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (a x k : ℂ) * χ (k : ZMod q) * (((if (k : ℝ) ≤ x - y then (1 : ℂ) else 0)) - Jv k)‖
        ≤ (110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x)) + D * x ^ (ε / 8))
          + (110 * (D * x ^ (ε / 8)) * (x / (x ^ (0.45 - 2 * ε / 3))) * (1 + Real.log (2 * x)) + D * x ^ (ε / 8)) :=
          add_le_add hxcut hvcut
      _ ≤ 240 * D * x ^ (0.55 + 11 * ε / 12) := hfin
  rw [hconv, hwin]
  simp only [hhalf]
  simpa only [hJxdef, hJvdef] using hkey



/-- Page 25, the finite critical line polynomial is continuous in height. -/
private theorem criticalPolynomial_continuous (a : ℝ → ℕ → ℝ) {x : ℝ} (_hx : 3 ≤ x)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : Continuous (fun t => criticalPolynomial a x t χ) := by
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  unfold criticalPolynomial
  apply continuous_finsetSum
  intro k hk
  have hk0 : k ≠ 0 := by
    have hh := (Finset.mem_Ioc.mp hk).1
    omega
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  exact continuous_const.div (hhalf.const_cpow (Or.inl hkC))
    (fun t => Complex.cpow_ne_zero_iff.mpr (Or.inl hkC))

/-- Page 25, the Perron kernel is continuous in height on every positive window. -/
private theorem windowKernel_continuous {x y : ℝ} (hx : 0 < x) (hxy : 0 < x - y) :
    Continuous (fun t =>
      ((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t) := by
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  apply ((hhalf.const_cpow (Or.inl (by exact_mod_cast ne_of_gt hx))).sub
    (hhalf.const_cpow (Or.inl (by exact_mod_cast ne_of_gt hxy)))).div hhalf
  intro t ht
  have hre := congrArg Complex.re ht
  simp [Thm4.half] at hre

/-- Page 25, display 4.4 with an explicit bound for the polynomial.
The remaining analytic input is only a uniform bound on F at low heights. -/
private theorem low_height_remainder_bound (a : ℝ → ℕ → ℝ) {x y M : ℝ}
    (hx : 3 ≤ x) (hy : 0 ≤ y) (hyw : y ≤ referenceWidth x) (hM : 0 ≤ M)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hF : ∀ t : ℝ, |t| ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) →
      ‖criticalPolynomial a x t χ‖ ≤ M) :
    ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
      (y : ℂ) * lowCenter a x χ‖ ≤
        ‖(1 / (2 * Real.pi) : ℂ)‖ * 4 * M *
          (Real.exp (Real.log x ^ (1 / 3 : ℝ))) ^ 2 *
          (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 := by
  let T : ℝ := Real.exp (Real.log x ^ (1 / 3 : ℝ))
  let F : ℝ → ℂ := fun t => criticalPolynomial a x t χ
  let K : ℝ → ℂ := fun t =>
    ((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t
  let L : ℝ → ℂ := fun t => (y : ℂ) * (x : ℂ) ^ (Thm4.half t - 1)
  have hx0 : 0 < x := by linarith
  have hyhalf : y ≤ x / 2 := hyw.trans (referenceWidth_lt_half_x hx).le
  have hxy : 0 < x - y := by linarith
  have hT : 1 ≤ T := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith : 1 ≤ x)) _
  have hT0 : 0 ≤ T := by linarith
  have hhalf : Continuous Thm4.half := by unfold Thm4.half; fun_prop
  have hFc : Continuous F := criticalPolynomial_continuous a hx χ
  have hKc : Continuous K := windowKernel_continuous hx0 hxy
  have hLc : Continuous L := continuous_const.mul
    ((hhalf.sub continuous_const).const_cpow (Or.inl (by exact_mod_cast ne_of_gt hx0)))
  have he : windowContour a x y T χ - (y : ℂ) * lowCenter a x χ =
      (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, F t * (K t - L t) := by
    simp_rw [mul_sub]
    have hiK : IntervalIntegrable (fun t => F t * K t) MeasureTheory.volume (-T) T :=
      (hFc.mul hKc).intervalIntegrable _ _
    have hiL : IntervalIntegrable (fun t => F t * L t) MeasureTheory.volume (-T) T :=
      (hFc.mul hLc).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hiK hiL]
    have hlin : (∫ t in (-T)..T, F t * L t) =
        (y : ℂ) * ∫ t in (-T)..T, F t * (x : ℂ) ^ (Thm4.half t - 1) := by
      dsimp [L]
      simp_rw [show ∀ t : ℝ, F t * ((y : ℂ) * (x : ℂ) ^ (Thm4.half t - 1)) =
        (y : ℂ) * (F t * (x : ℂ) ^ (Thm4.half t - 1)) by intro t; ring]
      exact intervalIntegral.integral_const_mul _ _
    rw [hlin]
    dsimp [windowContour, lowCenter, T, F, K]
    ring
  have hb : ∀ t ∈ Set.uIoc (-T) T,
      ‖F t * (K t - L t)‖ ≤ M * (2 * T) * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hs : ‖Thm4.half t - 1‖ ≤ 2 * T := by
      have he : Thm4.half t - 1 = (- (1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
        unfold Thm4.half
        push_cast
        ring
      rw [he]
      calc
        _ ≤ ‖(- (1 / 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = (1 / 2 : ℝ) + |t| := by simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 * T := by linarith
    have hkernel := perron_kernel_first_order_bound hx0 hy hyhalf t
    change ‖K t - L t‖ ≤ _ at hkernel
    rw [norm_mul]
    calc
      _ ≤ M * (‖Thm4.half t - 1‖ * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2) :=
        mul_le_mul (hF t htT) hkernel (norm_nonneg _) hM
      _ ≤ M * ((2 * T) * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2) := by gcongr
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [he, norm_mul]
  have htlen : |T - -T| = 2 * T := by rw [abs_of_nonneg (by linarith)]; ring
  rw [htlen] at hi
  have hmul := mul_le_mul_of_nonneg_left hi (norm_nonneg (1 / (2 * Real.pi) : ℂ))
  convert hmul using 1; dsimp [T]; ring

/-- Page 25, display 4.4 follows from a uniform logarithmic polynomial bound.
This separates the coefficient moment input from the contour calculation. -/
private theorem low_height_of_log_bound (a : ℝ → ℕ → ℝ) (C D X : ℝ)
    (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hF : ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D) :
    ∀ A : ℝ, 0 < A → ∃ K Y : ℝ, ∀ x : ℝ, Y ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ K * y * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨Xlog, hlog⟩ := Filter.eventually_atTop.mp
    (eventually_log_power_le_low_height (D + A))
  let N : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖
  let K : ℝ := N * 4 * C * (2 : ℝ) ^ (3 / 2 : ℝ)
  have hK : 0 ≤ K := by dsimp [K, N]; positivity
  refine ⟨K, max X (max Xlog 3), ?_⟩
  intro x hx q hq χ y hy hyw
  simp only [max_le_iff] at hx
  obtain ⟨hxX, hxlog, hx3⟩ := hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hy0 : 0 ≤ y := by linarith
  let h : ℝ := Real.log x ^ (1 / 3 : ℝ)
  have hb := low_height_remainder_bound a hx3 hy0 hyw
    (show 0 ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D by positivity) χ
    (fun t ht => hF x hxX q hq χ t)
  have hscale : x ^ (1 / 2 : ℝ) * (x / 2) ^ (-(3 / 2 : ℝ)) =
      (2 : ℝ) ^ (3 / 2 : ℝ) / x := by
    rw [Real.div_rpow hx0.le (by norm_num)]
    calc
      _ = (x ^ (1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) / (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
      _ = x ^ (-1 : ℝ) / (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hx0]
        norm_num
      _ = x⁻¹ / ((2 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg_one, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) / x := by rw [div_inv_eq_mul, div_eq_mul_inv]; ring
  have hwidth : y ≤ x * Real.exp (-3 * h) := hyw
  have hexp : (Real.exp h) ^ 2 * Real.exp (-3 * h) = Real.exp (-h) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsave : Real.log x ^ D * Real.exp (-h) ≤ Real.log x ^ (-A) := by
    have he : Real.log x ^ D = Real.log x ^ (D + A) * Real.log x ^ (-A) := by
      rw [← Real.rpow_add hl0]
      congr 1
      ring
    rw [he]
    calc
      _ ≤ Real.exp h * Real.log x ^ (-A) * Real.exp (-h) := by
        gcongr
        exact hlog x hxlog
      _ = Real.log x ^ (-A) := by
        rw [mul_right_comm, ← Real.exp_add]
        simp
  have hs : N * 4 * (C * x ^ (1 / 2 : ℝ) * Real.log x ^ D) *
      (Real.exp h) ^ 2 * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 =
      K * Real.log x ^ D * (Real.exp h) ^ 2 * (y / x) * y := by
    dsimp [K]
    calc
      _ = (N * 4 * C * Real.log x ^ D * (Real.exp h) ^ 2 * y ^ 2) *
        (x ^ (1 / 2 : ℝ) * (x / 2) ^ (-(3 / 2 : ℝ))) := by ring
      _ = _ := by rw [hscale]; ring
  change _ ≤ N * 4 * (C * x ^ (1 / 2 : ℝ) * Real.log x ^ D) *
    (Real.exp h) ^ 2 * (x / 2) ^ (-(3 / 2 : ℝ)) * y ^ 2 at hb
  rw [hs] at hb
  have hyx : y / x ≤ Real.exp (-3 * h) := (div_le_iff₀ hx0).mpr (by simpa [mul_comm] using hwidth)
  calc
    _ ≤ K * Real.log x ^ D * (Real.exp h) ^ 2 * (y / x) * y := hb
    _ ≤ K * Real.log x ^ D * (Real.exp h) ^ 2 * Real.exp (-3 * h) * y := by gcongr
    _ = K * y * (Real.log x ^ D * Real.exp (-h)) := by
      rw [mul_assoc (K * Real.log x ^ D), hexp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (mul_nonneg hK hy0)

/-- Page 25, an auxiliary first divisor moment for the displayed bound on F.
Reuses Mathlib's exact divisor summatory identity and harmonic estimate. -/
private theorem divisor_sum_bound (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ)) ≤
      (N : ℝ) * (1 + Real.log N) := by
  have hid := congrArg (fun n : ℕ => (n : ℝ))
    (ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N)
  simp only [Nat.cast_sum, ArithmeticFunction.sigma_zero_apply] at hid
  rw [hid]
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (N : ℝ) / (n : ℝ) :=
      Finset.sum_le_sum (fun n hn => Nat.cast_div_le)
    _ = (N : ℝ) * (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum, hset]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg N)

/-- Page 25, the displayed polynomial bound holds without a logarithmic loss
when the divisor exponent is nonpositive. -/
private theorem polynomial_bound_nonpositive {B : ℝ} (hB : B ≤ 0) (a : ℝ → ℕ → ℝ)
    {C : ℝ} (ha : ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    {x : ℝ} (hx : 3 ≤ x) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖criticalPolynomial a x t χ‖ ≤ 4 * |C| * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  let S := Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊
  have hcard : (S.card : ℝ) ≤ 2 * x := by
    calc
      _ ≤ (⌊2 * x⌋₊ : ℝ) := by
        dsimp [S]
        rw [Nat.card_Ioc]
        exact_mod_cast Nat.sub_le ⌊2 * x⌋₊ ⌊x / 2⌋₊
      _ ≤ _ := Nat.floor_le (by linarith : 0 ≤ 2 * x)
  have hterm : ∀ k ∈ S,
      ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ ≤
        |C| * (x / 2) ^ (-(1 / 2 : ℝ)) := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hτ : 1 ≤ (k.divisors.card : ℝ) := by
      have h : 1 ≤ k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
      exact_mod_cast h
    have hpow : (k.divisors.card : ℝ) ^ B ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hτ hB
    have hcoeff : |a x k| ≤ |C| := by
      calc
        _ ≤ C * (k.divisors.card : ℝ) ^ B := ha x k
        _ ≤ |C| * (k.divisors.card : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ _ := mul_le_of_le_one_right (abs_nonneg C) hpow
    have htwist : ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ |C| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans hcoeff
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk0), hre, div_eq_mul_inv,
      ← Real.rpow_neg hkpos.le]
    apply mul_le_mul htwist _ (Real.rpow_nonneg hkpos.le _) (abs_nonneg C)
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2)
      ((Nat.floor_lt' hk0).mp hkl).le (by norm_num)
  have hxs : x * x ^ (-(1 / 2 : ℝ)) = x ^ (1 / 2 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hscale : x * (x / 2) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow hx0.le (by norm_num), ← mul_div_assoc, hxs,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have htwo : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  calc
    _ ≤ ∑ k ∈ S, ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ (S.card : ℝ) * (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) := by
      simpa using Finset.sum_le_sum hterm
    _ ≤ (2 * x) * (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = (2 * |C|) * ((2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
      calc
        _ = (2 * |C|) * (x * (x / 2) ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [hscale]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left htwo
        (show 0 ≤ 2 * |C| * x ^ (1 / 2 : ℝ) by positivity)
      nlinarith

/-- Page 25, the polynomial logarithmic bound has exponent zero for every
nonpositive divisor exponent. -/
private theorem divisor_log_bound_nonpositive (B : ℝ) (hB : B ≤ 0) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C D X : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D := by
  obtain ⟨C, ha⟩ := ha
  refine ⟨4 * |C|, 0, 3, by positivity, le_rfl, ?_⟩
  intro x hx q hq χ t
  simpa using polynomial_bound_nonpositive hB a ha hx χ t

/-- Page 25, the displayed polynomial bound for divisor exponents at most one.
The first divisor moment gives one logarithmic loss. -/
private theorem polynomial_bound_le_one {B : ℝ} (hB : B ≤ 1) (a : ℝ → ℕ → ℝ)
    {C : ℝ} (ha : ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    {x : ℝ} (hx : 3 ≤ x) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖criticalPolynomial a x t χ‖ ≤ 12 * |C| * x ^ (1 / 2 : ℝ) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl1 : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).2
    exact le_of_lt (Real.exp_one_lt_d9.trans
      (show (2.7182818286 : ℝ) < 3 by norm_num)) |>.trans hx
  have hl0 : 0 ≤ Real.log x := by linarith
  let S := Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊
  let N := ⌊2 * x⌋₊
  have hN1 : (1 : ℕ) ≤ N := (Nat.le_floor_iff (by linarith : 0 ≤ 2 * x)).mpr (by norm_num; linarith)
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNx : (N : ℝ) ≤ 2 * x := Nat.floor_le (by linarith : 0 ≤ 2 * x)
  have hsubset : S ⊆ Finset.Ioc 0 N := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨by omega, hku⟩
  have hsum : (∑ k ∈ S, (k.divisors.card : ℝ)) ≤ (2 * x) * (3 * Real.log x) := by
    have hlogN : Real.log N ≤ Real.log (2 * x) := Real.log_le_log hN0 hNx
    have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    have hlog2x : 1 + Real.log (2 * x) ≤ 3 * Real.log x := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
      linarith
    calc
      _ ≤ ∑ k ∈ Finset.Ioc 0 N, (k.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k hk hnot => Nat.cast_nonneg _)
      _ ≤ (N : ℝ) * (1 + Real.log N) := divisor_sum_bound N
      _ ≤ (N : ℝ) * (1 + Real.log (2 * x)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ (2 * x) * (1 + Real.log (2 * x)) :=
        mul_le_mul_of_nonneg_right hNx (by have := Real.log_nonneg (by linarith : 1 ≤ 2 * x); linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog2x (by linarith)
  have hterm : ∀ k ∈ S,
      ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ ≤
        |C| * (k.divisors.card : ℝ) * (x / 2) ^ (-(1 / 2 : ℝ)) := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hτ : 1 ≤ (k.divisors.card : ℝ) := by
      have h : 1 ≤ k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
      exact_mod_cast h
    have hpow : (k.divisors.card : ℝ) ^ B ≤ (k.divisors.card : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hτ hB
    have hcoeff : |a x k| ≤ |C| * (k.divisors.card : ℝ) := by
      calc
        _ ≤ C * (k.divisors.card : ℝ) ^ B := ha x k
        _ ≤ |C| * (k.divisors.card : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    have htwist : ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ |C| * (k.divisors.card : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans hcoeff
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk0), hre,
      div_eq_mul_inv, ← Real.rpow_neg hkpos.le]
    apply mul_le_mul htwist _ (Real.rpow_nonneg hkpos.le _) (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x / 2)
      ((Nat.floor_lt' hk0).mp hkl).le (by norm_num)
  have hxs : x * x ^ (-(1 / 2 : ℝ)) = x ^ (1 / 2 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hscale : x * (x / 2) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow hx0.le (by norm_num), ← mul_div_assoc, hxs,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have htwo : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  calc
    _ ≤ ∑ k ∈ S, ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S, |C| * (k.divisors.card : ℝ) * (x / 2) ^ (-(1 / 2 : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) * ∑ k ∈ S, (k.divisors.card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (|C| * (x / 2) ^ (-(1 / 2 : ℝ))) * ((2 * x) * (3 * Real.log x)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (6 * |C| * Real.log x) * ((2 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
      calc
        _ = (6 * |C| * Real.log x) * (x * (x / 2) ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [hscale]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left htwo
        (show 0 ≤ 6 * |C| * Real.log x * x ^ (1 / 2 : ℝ) by positivity)
      nlinarith

/-- Page 25, the polynomial logarithmic bound for divisor exponents at most one. -/
private theorem divisor_log_bound_le_one (B : ℝ) (hB : B ≤ 1) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C D X : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D := by
  obtain ⟨C, ha⟩ := ha
  refine ⟨12 * |C|, 1, 3, by positivity, by norm_num, ?_⟩
  intro x hx q hq χ t
  simpa using polynomial_bound_le_one hB a ha hx χ t

/-- Page 25, display 4.4 for every divisor exponent at most one.
This uses the first divisor moment and no OPEN leaf. -/
private theorem low_height_comparison_le_one (B : ℝ) (hB : B ≤ 1) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ C * y * Real.log x ^ (-A) := by
  obtain ⟨C, D, X, hC, hD, hF⟩ := divisor_log_bound_le_one B hB a ha
  exact low_height_of_log_bound a C D X hC hD hF

private theorem card_divisors_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

private theorem divisor_pow_succ_le (r n : ℕ) :
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
          _ ≤ _ := card_divisors_mul_le d (n / d)
      have hτR : (n.divisors.card : ℝ) ≤
          (d.divisors.card : ℝ) * ((n / d).divisors.card : ℝ) := by
        exact_mod_cast hτ
      simpa only [mul_pow] using
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n.divisors.card) hτR r

private theorem divisor_harmonic_recurrence (r M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ (r + 1) / n) ≤
      (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ r / n) ^ 2 := by
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
  calc
    (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ (r + 1) / n)
        ≤ ∑ n ∈ Finset.Icc 1 M,
            (∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ r *
              ((n / d).divisors.card : ℝ) ^ r) / n := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right (divisor_pow_succ_le r n) (Nat.cast_nonneg _)
    _ = ∑ p ∈ s, (p.2.divisors.card : ℝ) ^ r * ((p.1 / p.2).divisors.card : ℝ) ^ r / p.1 := by
      simp_rw [Finset.sum_div]
      exact Finset.sum_sigma' _ _ _
    _ ≤ _ := hsum
    _ = (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ r / n) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

private theorem divisor_harmonic_log_bound (r M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ r / n) ≤ (1 + Real.log M) ^ (2 ^ r) := by
  induction r with
  | zero =>
    simpa only [pow_zero, pow_one, one_div,
      harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log M
  | succ r ih =>
    apply (divisor_harmonic_recurrence r M).trans
    calc
      (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ r / n) ^ 2 ≤
          ((1 + Real.log M) ^ (2 ^ r)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ih 2
      _ = _ := by rw [← pow_mul, pow_succ]

set_option maxHeartbeats 4000000 in
/-- For divisor exponent above one, the polynomial is bounded by a fixed power of
`log x` after the `x ^ (1/2)` factor.  The exponent is `2 ^ ⌈B⌉`. -/
private theorem polynomial_bound_of_harmonic_moment {B : ℝ} (hB : 1 < B) (a : ℝ → ℕ → ℝ)
    {C₀ : ℝ} (ha : ∀ x k, |a x k| ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B)
    {x : ℝ} (hx : 3 ≤ x) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖criticalPolynomial a x t χ‖ ≤
      (2 ^ (1 / 2 : ℝ) * |C₀| * 3 ^ (2 ^ ⌈B⌉₊)) * x ^ (1 / 2 : ℝ) *
        Real.log x ^ ((2 ^ ⌈B⌉₊ : ℕ) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hC0 : (0 : ℝ) ≤ |C₀| := abs_nonneg C₀
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = ⌈B⌉₊ := ⟨⌈B⌉₊, rfl⟩
  rw [← hr]
  have hrB : B ≤ (r : ℝ) := by rw [hr]; exact Nat.le_ceil B
  have hr1 : 1 ≤ r := by rw [hr]; exact Nat.one_le_ceil_iff.mpr (by linarith)
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans Real.exp_one_lt_d9.le (by linarith)
  have hlx0 : 0 ≤ Real.log x := le_trans (by norm_num) hlx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊2 * x⌋₊ := ⟨⌊2 * x⌋₊, rfl⟩
  have hNx : (N : ℝ) ≤ 2 * x := by rw [hN]; exact Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.le_floor (by push_cast; linarith)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    rw [hN]
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro h
      have := Nat.floor_eq_zero.mp h
      linarith)
  -- per-term bound
  have hterm : ∀ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ ≤
        |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ r / (k : ℝ) ^ (1 / 2 : ℝ) := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hdiv1 : 1 ≤ ((k.divisors.card : ℕ) : ℝ) := by
      have h : 1 ≤ k.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
      exact_mod_cast h
    have hpow0 : (0 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.rpow_nonneg (by positivity) _
    have hpowB : ((k.divisors.card : ℕ) : ℝ) ^ B ≤ ((k.divisors.card : ℕ) : ℝ) ^ r := by
      rw [← Real.rpow_natCast (((k.divisors.card : ℕ) : ℝ)) r]
      exact Real.rpow_le_rpow_of_exponent_le hdiv1 hrB
    have hcoeff : |a x k| ≤ |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ r := by
      have h1 : |a x k| ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B := ha x k
      have h2 : C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B ≤
          |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ B :=
        mul_le_mul_of_nonneg_right (le_abs_self C₀) hpow0
      have h3 : |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ B ≤
          |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left hpowB hC0
      exact h1.trans (h2.trans h3)
    have htwist : ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤
        |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine (mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans hcoeff
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk0), hre]
    exact div_le_div_of_nonneg_right htwist (Real.rpow_nonneg hkpos.le _)
  -- sum over the support, then over `Icc 1 N`
  have hsub : Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊ ⊆ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by rw [hN]; exact hku⟩
  have hmoment : (∑ k ∈ Finset.Icc 1 N, ((k.divisors.card : ℕ) : ℝ) ^ r / k) ≤
      (1 + Real.log N) ^ (2 ^ r) := divisor_harmonic_log_bound r N
  have hsplit : ∀ k ∈ Finset.Icc 1 N,
      ((k.divisors.card : ℕ) : ℝ) ^ r / (k : ℝ) ^ (1 / 2 : ℝ) =
        (((k.divisors.card : ℕ) : ℝ) ^ r / k) * (k : ℝ) ^ (1 / 2 : ℝ) := by
    intro k hk
    have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hdiv : (k : ℝ) ^ (1 / 2 : ℝ) / (k : ℝ) = (k : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hkpos]
      norm_num
    calc ((k.divisors.card : ℕ) : ℝ) ^ r / (k : ℝ) ^ (1 / 2 : ℝ)
        = ((k.divisors.card : ℕ) : ℝ) ^ r * ((k : ℝ) ^ (1 / 2 : ℝ) / (k : ℝ)) := by
          rw [hdiv, Real.rpow_neg hkpos.le, div_eq_mul_inv]
      _ = (((k.divisors.card : ℕ) : ℝ) ^ r / k) * (k : ℝ) ^ (1 / 2 : ℝ) := by
          field_simp
  have hlog3 : 1 + Real.log (N : ℝ) ≤ 3 * Real.log x := by
    have h1 : Real.log (N : ℝ) ≤ Real.log (2 * x) := Real.log_le_log hNpos hNx
    have h2 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
    have h3 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hbase : (1 + Real.log (N : ℝ)) ^ (2 ^ r) ≤ 3 ^ (2 ^ r) * Real.log x ^ (2 ^ r) := by
    have hb0 : 0 ≤ 1 + Real.log (N : ℝ) := by
      have hln : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
      linarith
    calc (1 + Real.log (N : ℝ)) ^ (2 ^ r) ≤ (3 * Real.log x) ^ (2 ^ r) :=
          pow_le_pow_left₀ hb0 hlog3 _
      _ = 3 ^ (2 ^ r) * Real.log x ^ (2 ^ r) := mul_pow _ _ _
  have hNsqrt : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (2 * x) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num)
  have h2x : (2 * x) ^ (1 / 2 : ℝ) = 2 ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) :=
    Real.mul_rpow (by norm_num) hx0.le
  have hlogx : Real.log x ^ (2 ^ r) = Real.log x ^ ((2 ^ r : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  unfold criticalPolynomial
  calc
    ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖
        ≤ ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
            ‖(a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ r / (k : ℝ) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
          |C₀| * ((k.divisors.card : ℕ) : ℝ) ^ r / (k : ℝ) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by
        exact div_nonneg (mul_nonneg hC0 (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg k) _))
    _ = ∑ k ∈ Finset.Icc 1 N,
          |C₀| * (((k.divisors.card : ℕ) : ℝ) ^ r / (k : ℝ) ^ (1 / 2 : ℝ)) :=
      Finset.sum_congr rfl (fun k _ => by rw [mul_div_assoc])
    _ = |C₀| * ∑ k ∈ Finset.Icc 1 N,
          (((k.divisors.card : ℕ) : ℝ) ^ r / (k : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Finset.mul_sum]
    _ = |C₀| * ∑ k ∈ Finset.Icc 1 N,
          (((k.divisors.card : ℕ) : ℝ) ^ r / k) * (k : ℝ) ^ (1 / 2 : ℝ) := by
      congr 1
      exact Finset.sum_congr rfl (fun k hk => hsplit k hk)
    _ ≤ |C₀| * ∑ k ∈ Finset.Icc 1 N,
          (((k.divisors.card : ℕ) : ℝ) ^ r / k) * (N : ℝ) ^ (1 / 2 : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ hC0
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hkN : (k : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hk).2
      have hfrac : 0 ≤ ((k.divisors.card : ℕ) : ℝ) ^ r / k :=
        div_nonneg (by positivity) (Nat.cast_nonneg k)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hkpos.le hkN (by norm_num)) hfrac
    _ = |C₀| * (N : ℝ) ^ (1 / 2 : ℝ) *
          ∑ k ∈ Finset.Icc 1 N, ((k.divisors.card : ℕ) : ℝ) ^ r / k := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ |C₀| * (2 * x) ^ (1 / 2 : ℝ) * (1 + Real.log (N : ℝ)) ^ (2 ^ r) := by
      have hA : (0 : ℝ) ≤ |C₀| * (2 * x) ^ (1 / 2 : ℝ) :=
        mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
      have hS : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N,
          ((k.divisors.card : ℕ) : ℝ) ^ r / k :=
        Finset.sum_nonneg (fun k _ => div_nonneg (by positivity) (Nat.cast_nonneg k))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hNsqrt hC0) hmoment hS hA
    _ ≤ |C₀| * (2 * x) ^ (1 / 2 : ℝ) * (3 ^ (2 ^ r) * Real.log x ^ (2 ^ r)) := by
      exact mul_le_mul_of_nonneg_left hbase
        (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _))
    _ = (2 ^ (1 / 2 : ℝ) * |C₀| * 3 ^ (2 ^ r)) * x ^ (1 / 2 : ℝ) *
          Real.log x ^ ((2 ^ r : ℕ) : ℝ) := by
      rw [h2x, hlogx]
      ring

/-- LEAF. Page 25, the displayed bound on F between 4.3 and 4.4.
Only a logarithmic divisor moment bound on the finite polynomial is required.
There is no contour, window comparison or mean value conclusion. -/
private theorem divisor_polynomial_log_bound (B : ℝ) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C D X : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖criticalPolynomial a x t χ‖ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ D := by
  by_cases hB : B ≤ 1
  · exact divisor_log_bound_le_one B hB a ha
  · obtain ⟨C₀, hC₀⟩ := ha
    refine ⟨2 ^ (1 / 2 : ℝ) * |C₀| * 3 ^ (2 ^ ⌈B⌉₊), ((2 ^ ⌈B⌉₊ : ℕ) : ℝ), 3,
      by positivity, by positivity, ?_⟩
    intro x hx q _ χ t
    exact polynomial_bound_of_harmonic_moment (not_le.mp hB) a hC₀ hx χ t

/-- Page 25, display 4.4.
Only the low height Taylor error is required. The divisor bound supplies
polynomial growth and the reference width absorbs every logarithmic loss.
CONDITIONAL on divisor_polynomial_log_bound. -/
private theorem low_height_comparison (B : ℝ) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ C * y * Real.log x ^ (-A) := by
  obtain ⟨C, D, X, hC, hD, hF⟩ := divisor_polynomial_log_bound B a ha
  exact low_height_of_log_bound a C D X hC hD hF

/-- Page 25, display 4.4 is proved for nonpositive divisor exponents.
This uses the clean exponent zero polynomial bound and no OPEN leaf. -/
private theorem low_height_comparison_nonpositive (B : ℝ) (hB : B ≤ 0) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (y : ℂ) * lowCenter a x χ‖ ≤ C * y * Real.log x ^ (-A) := by
  obtain ⟨C, D, X, hC, hD, hF⟩ := divisor_log_bound_nonpositive B hB a ha
  exact low_height_of_log_bound a C D X hC hD hF

/-- Page 25, the two high height pieces between displays 4.4 and 4.5.
The mean value input and the kernel bound control these pieces.
There is no coefficient or endpoint truncation conclusion. -/
private theorem high_height_comparison {ε : ℝ} (hε : 0 < ε) (hεu : ε < 1 / 10)
    (a : ℝ → ℕ → ℝ) (hm : MeanValue41 ε a) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
      ‖windowContour a x y (x ^ (0.45 - 2 * ε / 3)) χ -
        windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ‖ ≤
          C * y * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, X, hmean⟩ := hm A hA
  have hα : 0 < 0.45 - 2 * ε / 3 := by linarith
  obtain ⟨Xh, hh⟩ := Filter.eventually_atTop.mp
    (eventually_low_height_le_power hα)
  let N : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖
  refine ⟨2 * N * |C| * (2 : ℝ) ^ (1 / 2 : ℝ), max X (max Xh 3), ?_⟩
  intro x hx q hq hqx χ y hy hyw
  simp only [max_le_iff] at hx
  obtain ⟨hxX, hxH, hx3⟩ := hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hyhalf : y ≤ x / 2 := hyw.trans (referenceWidth_lt_half_x hx3).le
  have hxy : 0 < x - y := by linarith
  let T0 : ℝ := Real.exp (Real.log x ^ (1 / 3 : ℝ))
  let T1 : ℝ := x ^ (0.45 - 2 * ε / 3)
  let F : ℝ → ℂ := fun t => criticalPolynomial a x t χ
  let K : ℝ → ℂ := fun t =>
    ((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t
  let R : ℝ := (x / 2) ^ (-(1 / 2 : ℝ)) * y
  let M : ℝ := |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hp : ∀ σ ∈ ({-1, 1} : Finset ℝ),
      (∫ t in T0..T1, ‖F (σ * t)‖) ≤ M := by
    intro σ hσ
    have h := hmean x hxX q hq hqx χ σ hσ
    change (∫ t in T0..T1, ‖F (σ * t)‖) ≤ _ at h
    apply h.trans
    dsimp [M]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)) hL
  have hplus : (∫ t in T0..T1, ‖F t‖) ≤ M := by
    simpa using hp 1 (by simp)
  have hminus : (∫ t in T0..T1, ‖F (-t)‖) ≤ M := by
    simpa using hp (-1) (by simp)
  have ht := two_tail_norm_bound F K
    (criticalPolynomial_continuous a hx3 χ) (windowKernel_continuous hx0 hxy)
    (hh x hxH) (show 0 ≤ R by dsimp [R]; positivity)
    (fun t => perron_kernel_bound hx0 hy0 hyhalf t) hplus hminus
  have hpow : (x / 2) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg hx0.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hfinal : N * (2 * R * M) =
      (2 * N * |C| * (2 : ℝ) ^ (1 / 2 : ℝ)) * y * Real.log x ^ (-A) := by
    dsimp [R, M]
    calc
      _ = (2 * N * |C| * y * Real.log x ^ (-A)) *
        ((x / 2) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hpow]; ring
  unfold windowContour
  rw [← mul_sub, norm_mul]
  change N * ‖(∫ t in (-T1)..T1, F t * K t) -
      ∫ t in (-T0)..T0, F t * K t‖ ≤ _
  exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq hfinal

/-- Pages 11 and 25, the divisor bound controls each twisted coefficient
on the long polynomial support by every positive power of x. -/
private theorem twisted_coefficient_bound (B δ : ℝ) (hδ : 0 < δ)
    (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 ≤ x → ∀ q : ℕ,
    ∀ χ : DirichletCharacter ℂ q, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 2 * x →
      ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ D * x ^ δ := by
  obtain ⟨C, hcoeff⟩ := ha
  obtain ⟨K, hK, hk⟩ := coeff_small_power_any B δ hδ
  let b : ℕ → ℂ := fun n => if n = 0 then 0 else ((n.divisors.card : ℝ) ^ B : ℝ)
  have hb : Thm4.CoeffBound b B := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [b, ite_true, norm_zero]
      positivity
    · simp only [b, hn, ite_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact le_rfl
  refine ⟨|C| * K * (2 : ℝ) ^ δ, by positivity, ?_⟩
  intro x hx q χ k hk1 hkx
  have hk0 : k ≠ 0 := by omega
  have hdiv : (k.divisors.card : ℝ) ^ B ≤ K * (k : ℝ) ^ δ := by
    simpa only [b, hk0, ite_false, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hk b hb k hk1
  calc
    ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ |a x k| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)
    _ ≤ C * (k.divisors.card : ℝ) ^ B := hcoeff x k
    _ ≤ |C| * (k.divisors.card : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C| * (K * (k : ℝ) ^ δ) := mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)
    _ ≤ |C| * (K * (2 * x) ^ δ) := by
      gcongr
    _ = (|C| * K * (2 : ℝ) ^ δ) * x ^ δ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ x)]
      ring


/-- LEAF. Pages 24 and 25, Lemma 11, displays 4.1, 4.3, 4.4 and 4.5.
Perron comparison with the normalized I1 mean, for both signs of height.
The finite centering error and widths below 2 use the divisor bound.
This input asserts no density, prime sandwich, discarded-region estimate
or coefficient construction. OPEN. -/
theorem perron_window_comparison (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      MeanValue41 ε a → WindowComparison ε a := by
  obtain ⟨η, hη, htrunc⟩ := truncated_perron_window B
  refine ⟨min η (1 / 10), lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη a ha hm
  have hεη' : ε < η := lt_of_lt_of_le hεη (min_le_left _ _)
  have hεu : ε < 1 / 10 := lt_of_lt_of_le hεη (min_le_right _ _)
  obtain ⟨Ct, Xt, ht⟩ := htrunc ε hε hεη' a ha
  let p : ℝ := 0.55 + 11 * ε / 12
  have hp : 0 < p := by dsimp [p]; linarith
  obtain ⟨D, hD, hd⟩ := twisted_coefficient_bound B p hp a ha
  intro A hA
  obtain ⟨Cl, Xl, hl⟩ := low_height_comparison B a ha A hA
  obtain ⟨Ch, Xh, hh⟩ := high_height_comparison hε hεu a hm A hA
  obtain ⟨Xw, hw⟩ := Filter.eventually_atTop.mp
    (reference_width_long (ε := 0) (by norm_num))
  let K : ℝ := |Ct| + |Cl| + |Ch|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨2 * K + 9 * D, max Xt (max Xl (max Xh (max Xw 3))), ?_⟩
  intro x hx q hq hqx χ y hy hyw
  simp only [max_le_iff] at hx
  obtain ⟨hxt, hxl, hxh, hxw, hx3⟩ := hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hw2 : 2 ≤ referenceWidth x := by
    have hs := hw x hxw
    have hr : 1 ≤ x ^ (11 / 20 + (0 : ℝ)) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have hwx : referenceWidth x ≤ x := referenceWidth_le_x hx1
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hP : 0 ≤ x ^ p := Real.rpow_nonneg hx0 _
  have hcoeff : ∀ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
      ‖(a x k : ℂ) * χ (k : ZMod q)‖ ≤ D * x ^ p := by
    intro k hk
    have hi := window_subset_I1 hx3 (by linarith : 0 ≤ referenceWidth x) le_rfl hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hi
    have hk1 : 1 ≤ k := by omega
    have hkx : (k : ℝ) ≤ 2 * x :=
      (by exact_mod_cast hku : (k : ℝ) ≤ (⌊2 * x⌋₊ : ℝ)).trans
        (Nat.floor_le (by linarith : 0 ≤ 2 * x))
    exact hd x hx1 q χ k hk1 hkx
  have hcomp : ∀ z : ℝ, 2 ≤ z → z ≤ referenceWidth x →
      ‖(∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
        (z : ℂ) * lowCenter a x χ‖ ≤ K * (z * Real.log x ^ (-A) + x ^ p) := by
    intro z hz hzw
    have ht' := ht x hxt q hq χ z hz hzw
    have hl' := hl x hxl q hq χ z hz hzw
    have hh' := hh x hxh q hq hqx χ z hz hzw
    have hz0 : 0 ≤ z := by linarith
    have ht'' : Ct * x ^ p ≤ |Ct| * x ^ p :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hP
    have hl'' : Cl * z * Real.log x ^ (-A) ≤ |Cl| * z * Real.log x ^ (-A) := by
      gcongr
      exact le_abs_self _
    have hh'' : Ch * z * Real.log x ^ (-A) ≤ |Ch| * z * Real.log x ^ (-A) := by
      gcongr
      exact le_abs_self _
    have he : (∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
        (z : ℂ) * lowCenter a x χ =
        ((∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
          windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ) +
        (windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ -
          windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ) +
        (windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
          (z : ℂ) * lowCenter a x χ) := by ring
    rw [he]
    have hn := (norm_add_le
      (((∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
        windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ) +
        (windowContour a x z (x ^ (0.45 - 2 * ε / 3)) χ -
        windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ))
      (windowContour a x z (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ -
        (z : ℂ) * lowCenter a x χ)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    have htP : 0 ≤ |Ct| * (z * Real.log x ^ (-A)) := by positivity
    have hlP : 0 ≤ |Cl| * x ^ p := by positivity
    have hhP : 0 ≤ |Ch| * x ^ p := by positivity
    dsimp [K]
    change _ ≤ Ct * x ^ p at ht'
    nlinarith
  have hc := center_from_continuous_comparison
    (fun k => (a x k : ℂ) * χ (k : ZMod q)) (lowCenter a x χ)
    hw2 hwx hK hL hP (mul_nonneg hD hP) hcoeff hcomp hy hyw
  change ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊,
    ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ ≤ _ at hc
  have hDP : 0 ≤ 9 * D * (y * Real.log x ^ (-A)) := by positivity
  change _ ≤ (2 * K + 9 * D) * (y * Real.log x ^ (-A) + x ^ p)
  nlinarith

/-- Page 26, pair the divisors d and p times d. Only products crossing gamma remain in the truncated Möbius sum. -/
theorem mobius_truncation_crossing {p m : ℕ} (hp : p.Prime) (hpm : p.Coprime m)
    (γ : ℝ) :
    (∑ d ∈ (p * m).divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ),
      (ArithmeticFunction.moebius d : ℝ)) =
    ∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ ∧ γ < ((p * d : ℕ) : ℝ)),
      (ArithmeticFunction.moebius d : ℝ) := by
  have hμ (d : ℕ) (hd : d ∈ m.divisors) :
      (ArithmeticFunction.moebius (p * d) : ℝ) = -(ArithmeticFunction.moebius d : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hpm.coprime_dvd_right (Nat.mem_divisors.mp hd).1),
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  rw [Finset.sum_filter, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image hpm.mul_injOn_divisors, Finset.sum_product]
  rw [hp.divisors, Finset.sum_pair (Ne.symm hp.ne_one)]
  simp only [one_mul]
  rw [← Finset.sum_add_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hμ d hd]
  have hle : (d : ℝ) ≤ (p : ℝ) * (d : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left d hp.pos
  simp only [Nat.cast_mul]
  by_cases hpd : (p : ℝ) * (d : ℝ) ≤ γ
  · have hdγ : (d : ℝ) ≤ γ := hle.trans hpd
    simp [hpd, hdγ, not_lt.mpr hpd]
  · by_cases hdγ : (d : ℝ) ≤ γ
    · simp [hpd, hdγ, lt_of_not_ge hpd]
    · simp [hpd, hdγ]

/-- Page 26, inject the crossing products into the intermediate divisor band. Their Möbius coefficients have absolute value at most 1. -/
theorem mobius_truncation_band {p m : ℕ} (hp : p.Prime) (hpm : p.Coprime m)
    {γ w : ℝ} (hγ : 0 < γ) (hpw : (p : ℝ) < w) :
    |∑ d ∈ (p * m).divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ),
      (ArithmeticFunction.moebius d : ℝ)| ≤
    (((p * m).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) := by
  let S := m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ ∧ γ < ((p * d : ℕ) : ℝ))
  let T := (p * m).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)
  have hc : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun d : ℕ => p * d)
    · intro d hd
      obtain ⟨hdm, hdγ, hγd⟩ := Finset.mem_filter.mp hd
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left p (Nat.mem_divisors.mp hdm).1,
        mul_ne_zero hp.ne_zero (Nat.mem_divisors.mp hdm).2⟩, hγd.le, ?_⟩
      calc
        ((p * d : ℕ) : ℝ) = (p : ℝ) * (d : ℝ) := by norm_cast
        _ ≤ (p : ℝ) * γ := mul_le_mul_of_nonneg_left hdγ (Nat.cast_nonneg _)
        _ < w * γ := mul_lt_mul_of_pos_right hpw hγ
        _ = γ * w := mul_comm _ _
    · intro d hd e he hde
      exact Nat.eq_of_mul_eq_mul_left hp.pos hde
  rw [mobius_truncation_crossing hp hpm]
  calc
    _ ≤ ∑ d ∈ S, |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = (S.card : ℝ) := by simp
    _ ≤ (T.card : ℝ) := by exact_mod_cast hc

/-- Page 26, P of z is squarefree because its prime factors are distinct. -/
theorem primorial_squarefree (z : ℝ) : Squarefree (Thm2.primorialBelow z) := by
  unfold Thm2.primorialBelow
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (Finset.mem_filter.mp hp).2.1.squarefree)
  change IsRelPrime p q
  rw [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2.1
    (Finset.mem_filter.mp hq).2.1).mpr hpq

/-- Pages 25 and 26, every prime divisor of P of z is less than z. -/
theorem prime_lt_of_dvd_primorial {p : ℕ} {z : ℝ} (hp : p.Prime)
    (hd : p ∣ Thm2.primorialBelow z) : (p : ℝ) < z := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  obtain ⟨hqprime, hqz⟩ := (Finset.mem_filter.mp hq).2
  have he : p = q := ((Nat.dvd_prime hqprime).mp hpq).resolve_left hp.ne_one
  simpa only [he] using hqz


/-- Page 26, the intermediate-band truncation for a squarefree integer. A prime divisor pairs the two halves of its divisor set. -/
theorem squarefree_mobius_truncation (N : ℕ) (hN : Squarefree N)
    {γ w : ℝ} (hγ : 1 ≤ γ)
    (hw : ∀ p : ℕ, p.Prime → p ∣ N → (p : ℝ) < w) :
    |(if N = 1 then (1 : ℝ) else 0) -
      ∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ),
        (ArithmeticFunction.moebius d : ℝ)| ≤
    ((N.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) := by
  by_cases hN1 : N = 1
  · subst N
    simp only [Nat.divisors_one, Finset.filter_singleton, Nat.cast_one]
    rw [ite_eq_left hγ]
    simp
  · let p := N.minFac
    have hp : p.Prime := Nat.minFac_prime hN1
    have hpd : p ∣ N := Nat.minFac_dvd N
    have hfactor : p * (N / p) = N := Nat.mul_div_cancel' hpd
    have hcop : p.Coprime (N / p) := Nat.coprime_of_squarefree_mul (hfactor.symm ▸ hN)
    have hb := mobius_truncation_band hp hcop (by linarith : 0 < γ) (hw p hp hpd)
    rw [hfactor] at hb
    simpa only [ite_eq_right hN1, zero_sub, abs_neg] using hb

/-- Page 27, an auxiliary finite Rankin reduction for the reciprocal divisor tail.
It leaves a prime product explicit and does not assert Hildebrand 4.13.
Reuses Mathlib's multiplicative divisor Euler product. -/
theorem squarefree_reciprocal_rankin (N : ℕ) (hN : Squarefree N)
    {γ α : ℝ} (hγ : 0 < γ) (hα0 : 0 ≤ α) (hα : α < 1) :
    (∑ d ∈ N.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ)) ≤
      γ ^ (-α) * ∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (α - 1)) := by
  let f : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) ^ (α - 1), by
    simp only [Nat.cast_zero, Real.zero_rpow (by linarith : α - 1 ≠ 0)]⟩
  have hf : f.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨by simp [f], ?_⟩
    intro m n hm hn hmn
    change ((m * n : ℕ) : ℝ) ^ (α - 1) = (m : ℝ) ^ (α - 1) * (n : ℝ) ^ (α - 1)
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hp : (∑ d ∈ N.divisors, (d : ℝ) ^ (α - 1)) =
      ∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (α - 1)) := by
    simpa only [f, ArithmeticFunction.coe_mk] using
      (hf.prodPrimeFactors_one_add_of_squarefree hN).symm
  let S := N.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ))
  calc
    _ ≤ ∑ d ∈ S, γ ^ (-α) * (d : ℝ) ^ (α - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdγ := (Finset.mem_filter.mp hd).2
      have hd0 : 0 < (d : ℝ) := hγ.trans_le hdγ
      have hpow := Real.rpow_le_rpow_of_nonpos hγ hdγ (neg_nonpos.mpr hα0)
      calc
        1 / (d : ℝ) = (d : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
        _ = (d : ℝ) ^ (-α) * (d : ℝ) ^ (α - 1) := by
          rw [← Real.rpow_add hd0]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = γ ^ (-α) * ∑ d ∈ S, (d : ℝ) ^ (α - 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ γ ^ (-α) * ∑ d ∈ N.divisors, (d : ℝ) ^ (α - 1) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d hd hdS => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hγ.le _)
    _ = _ := by rw [hp]


/-- Auxiliary Perron kernel bound for the page 22 contour calculation. -/
theorem perron_remainder_bound490 {y c T : ℝ}
    (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) -
        (if 1 < y then 1 else 0)‖ ≤ y ^ c / (Real.pi * T * |Real.log y|) := by
  rw [perron_rescale_general hy hc]
  let a : ℝ := c / 2
  let z : ℝ := y ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hy a
  have hlog : Real.log z = a * Real.log y := Real.log_rpow hy a
  have hbranch : (1 < z) ↔ (1 < y) := by
    rw [Real.one_lt_rpow_iff_of_pos hy]
    simp [ha, ha.not_gt]
  have hz1 : z ≠ 1 := by
    intro h
    have hh := congrArg Real.log h
    rw [hlog, Real.log_one] at hh
    exact (mul_ne_zero ha.ne' (Real.log_ne_zero_of_pos_of_ne_one hy hy1)) hh
  have h := perron_kernel_two z hz hz1 (T / a) (div_pos hT ha)
  have hpow : z ^ 2 = y ^ c := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    congr 1
    dsimp [a]
    ring
  simp only [hbranch, hpow, hlog, abs_mul, abs_of_pos ha] at h
  have hden : Real.pi * (T / a) * (a * |Real.log y|) = Real.pi * T * |Real.log y| := by
    field_simp
  rw [hden] at h
  exact h

end LeanLab.BHP1997.Decomp312c
