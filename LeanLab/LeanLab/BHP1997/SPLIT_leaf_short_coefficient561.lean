/-
Independent split of the short coefficient replacement step of the periodic
kernel reduction.  The short block mass is read off the divisor type bound, the
replacement at a single even frequency is bounded by a logarithmic saving times
that mass, the number of even frequencies is counted, and the elementary
thresholds are collected separately.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561n
import LeanLab.Tolev2009.DivisorMoment

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- All divisor moments are bounded by the harmonic sum: for every `k` there are
exponents `e d` with `∑_{n ≤ N} d(n)^k ≤ N H_N^e` and `∑_{n ≤ N} d(n)^k / n ≤ H_N^d`.
Joint induction on `k`, using the two step lemmas of the divisor-moment module. -/
private theorem divMoment_all561 : ∀ k : ℕ, ∃ e d : ℕ,
    (∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ k ≤
      (N : ℝ) * LeanLab.HeathBrown1985.Hn N ^ e) ∧
    (∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ k / (n : ℝ) ≤
      LeanLab.HeathBrown1985.Hn N ^ d) := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, 1, ?_, ?_⟩
    · intro N
      have h1 : ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 0 =
          ((Finset.Icc 1 N).card : ℝ) := by simp
      rw [h1, Nat.card_Icc]
      simp
    · intro N
      have h1 : ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 0 / (n : ℝ) =
          LeanLab.HeathBrown1985.Hn N := by
        simp [LeanLab.HeathBrown1985.Hn, one_div]
      rw [h1]
      simp
  | succ k ih =>
    obtain ⟨e, d, hP, hQ⟩ := ih
    exact ⟨e + d, 2 * d, fun N =>
      LeanLab.Tolev2009.DivisorMoment.moment_step N k e d
        (fun M _ => hP M) (hQ N),
      fun N => LeanLab.Tolev2009.DivisorMoment.reciprocal_step N k d
        (fun M _ => hQ M)⟩

/-- LEAF. Counting step.  The even frequencies form an arithmetic progression of
even numbers inside an interval whose length is the frequency height, so their
number is at most twice that height.  Only cardinality is used, with no analytic
input. -/
theorem leaf_short_frequency_card561 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ((frequencies512 ε x).card : ℝ) ≤
        2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  refine ⟨3, fun x hx => ?_⟩
  have hx3 : (3 : ℝ) ≤ x := hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hcpos : (0 : ℝ) < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) := by
    have h1 : (0 : ℝ) < 11 / 20 + ε := by linarith
    have h2 : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5 : ℝ) := by norm_num
    exact mul_pos h1 h2
  have hxC : (1 : ℝ) ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    Real.one_le_rpow hx1 hcpos.le
  have hstep1 : ((frequencies512 ε x).card : ℝ) ≤
      ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).card : ℝ) := by
    rw [frequencies512]
    exact_mod_cast Finset.card_filter_le _ _
  have hA : (⌈x⌉₊ : ℝ) ≤ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ + 1 := by
    have h1 : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    have h2 : x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) <
        ((⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h3 : (1 : ℝ) ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := hxC
    linarith
  have hle : (⌈x⌉₊ : ℕ) ≤ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ + 1 := by
    exact_mod_cast hA
  have hstep2 : ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).card : ℝ) ≤
      x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) + 1 := by
    rw [Nat.card_Icc, Nat.cast_sub hle]
    push_cast
    have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have h2 : ((⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℕ) : ℝ) ≤
        x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
      Nat.floor_le (by positivity)
    linarith
  calc ((frequencies512 ε x).card : ℝ)
      ≤ ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).card : ℝ) :=
        hstep1
    _ ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) + 1 := hstep2
    _ ≤ 2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by linarith

/-- LEAF. Mass of the short block.  From the divisor type bound alone, the sum of
the coefficient norms over the short support is at most a constant times the block
length times a single fixed power of the logarithm of x.  The exponent is returned
with the constant, because the divisor moment on a block of length about that
length costs a power of the logarithm growing with the divisor exponent. -/
theorem leaf_short_block_mass561 (B C₀ : ℝ) :
    ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ b : ℕ → ℂ,
        (∀ k : ℕ, ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ ≤
          K * length512 ε x * Real.log x ^ M := by
  set kk : ℕ := ⌈B⌉₊ with hkk
  obtain ⟨e, d, hP, hQ⟩ := divMoment_all561 kk
  refine ⟨max 1 C₀, ((e + 1 : ℕ) : ℝ), le_max_left _ _, ?_, ?_⟩
  · have : (1 : ℝ) ≤ ((e + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le e)
    linarith
  intro ε hε
  set θ : ℝ := 11 / 20 + ε with hθ
  have hθpos : 0 < θ := by rw [hθ]; linarith
  set ce : ℝ := 1 + Real.log 2 + θ with hce
  refine ⟨max 3 (Real.exp (max 2 (2 * max 1 C₀ * ce ^ e))), fun x hx b hb => ?_⟩
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hA0 : max 2 (2 * max 1 C₀ * ce ^ e) ≤ Real.log x := by
    have h1 : Real.exp (max 2 (2 * max 1 C₀ * ce ^ e)) ≤ x := le_trans (le_max_right _ _) hx
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hlog2 : (2 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hA0
  have hlog1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLdef : length512 ε x = x ^ θ := by rw [length512, ← hθ]
  have hLpos : (0 : ℝ) < length512 ε x := by
    rw [hLdef]; exact Real.rpow_pos_of_pos hx0 θ
  have hL1 : (1 : ℝ) ≤ length512 ε x := by
    rw [hLdef]; exact Real.one_le_rpow hx1 hθpos.le
  have hL0 : (0 : ℝ) ≤ length512 ε x := hLpos.le
  have h2Lpos : (0 : ℝ) < 2 * length512 ε x := by linarith
  have hfl1 : 1 ≤ ⌊length512 ε x⌋₊ := Nat.le_floor (by simpa using hL1)
  have hfl2 : 1 ≤ ⌊2 * length512 ε x⌋₊ :=
    Nat.le_floor (by simpa using (by linarith : (1 : ℝ) ≤ 2 * length512 ε x))
  have hBcast : ((⌊2 * length512 ε x⌋₊ : ℕ) : ℝ) ≤ 2 * length512 ε x :=
    Nat.floor_le (by linarith)
  have hBpos : (0 : ℝ) < ((⌊2 * length512 ε x⌋₊ : ℕ) : ℝ) := by
    have : (0 : ℕ) < ⌊2 * length512 ε x⌋₊ := by omega
    exact_mod_cast this
  -- pointwise comparison of the two powers of the divisor count
  have hcard1 : ∀ m : ℕ, 1 ≤ m → (1 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by
    intro m hm
    have hmem : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hpos : 0 < m.divisors.card := Finset.card_pos.mpr ⟨1, hmem⟩
    exact_mod_cast hpos
  have hpowB : ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℕ) : ℝ) ^ B ≤ ((m.divisors.card : ℕ) : ℝ) ^ kk := by
    intro m hm
    have h1 : (1 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := hcard1 m hm
    have h2 : B ≤ (kk : ℝ) := Nat.le_ceil B
    calc ((m.divisors.card : ℕ) : ℝ) ^ B ≤ ((m.divisors.card : ℕ) : ℝ) ^ (kk : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 h2
      _ = ((m.divisors.card : ℕ) : ℝ) ^ kk := Real.rpow_natCast _ _
  have hstepA : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ ≤
      C₀ * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
        ((m.divisors.card : ℕ) : ℝ) ^ B := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun m _ => hb m)
  have hHn : LeanLab.HeathBrown1985.Hn ⌊2 * length512 ε x⌋₊ ≤ ce * Real.log x := by
    have h1 : LeanLab.HeathBrown1985.Hn ⌊2 * length512 ε x⌋₊ ≤
        1 + Real.log ((⌊2 * length512 ε x⌋₊ : ℕ) : ℝ) :=
      LeanLab.HeathBrown1985.Hn_le _
    have h2 : Real.log ((⌊2 * length512 ε x⌋₊ : ℕ) : ℝ) ≤ Real.log (2 * length512 ε x) :=
      Real.log_le_log hBpos hBcast
    have h3 : Real.log (2 * length512 ε x) = Real.log 2 + θ * Real.log x := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hLpos), hLdef, Real.log_rpow hx0]
    have h4 : 1 + Real.log 2 + θ * Real.log x ≤ ce * Real.log x := by
      have h5 : 1 + Real.log 2 ≤ (1 + Real.log 2) * Real.log x := by nlinarith
      have h6 : θ ≤ θ * Real.log x := by nlinarith
      rw [hce]; nlinarith
    linarith
  have hHn0 : (0 : ℝ) ≤ LeanLab.HeathBrown1985.Hn ⌊2 * length512 ε x⌋₊ :=
    LeanLab.HeathBrown1985.Hn_nonneg _
  have hHnpow : LeanLab.HeathBrown1985.Hn ⌊2 * length512 ε x⌋₊ ^ e ≤
      (ce * Real.log x) ^ e :=
    pow_le_pow_left₀ hHn0 hHn e
  have hcelog0 : (0 : ℝ) ≤ ce * Real.log x := by
    have : (0 : ℝ) < ce := by rw [hce]; linarith
    positivity
  rcases le_total 0 C₀ with hC₀ | hC₀
  · have hstepB : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
        ((m.divisors.card : ℕ) : ℝ) ^ B ≤
        ∑ m ∈ Finset.Icc 1 ⌊2 * length512 ε x⌋₊, ((m.divisors.card : ℕ) : ℝ) ^ kk := by
      refine le_trans (Finset.sum_le_sum (fun m hm => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity))
      · rw [Finset.mem_Ioc] at hm
        exact hpowB m (by omega)
      · intro m hm
        simp only [Finset.mem_Ioc, Finset.mem_Icc] at hm ⊢
        exact ⟨by omega, hm.2⟩
    have hmom : ∑ m ∈ Finset.Icc 1 ⌊2 * length512 ε x⌋₊,
        ((m.divisors.card : ℕ) : ℝ) ^ kk ≤
          ((⌊2 * length512 ε x⌋₊ : ℕ) : ℝ) *
            LeanLab.HeathBrown1985.Hn ⌊2 * length512 ε x⌋₊ ^ e := hP _
    have hpow1 : (2 * C₀ * ce ^ e) ≤ Real.log x := by
      have h1 : C₀ ≤ max 1 C₀ := le_max_right _ _
      have h2 : (0 : ℝ) ≤ 2 * max 1 C₀ * ce ^ e := by positivity
      have h3 : 2 * C₀ * ce ^ e ≤ 2 * max 1 C₀ * ce ^ e := by
        refine mul_le_mul_of_nonneg_right (by linarith) ?_
        have hcepos : (0 : ℝ) < ce := by rw [hce]; linarith [hlog2pos, hθpos]
        positivity
      linarith [le_trans h3 (le_trans (le_max_right _ _) hA0)]
    calc ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖
        ≤ C₀ * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            ((m.divisors.card : ℕ) : ℝ) ^ B := hstepA
      _ ≤ C₀ * (((⌊2 * length512 ε x⌋₊ : ℕ) : ℝ) *
            LeanLab.HeathBrown1985.Hn ⌊2 * length512 ε x⌋₊ ^ e) := by
          refine mul_le_mul_of_nonneg_left (le_trans hstepB hmom) hC₀
      _ ≤ C₀ * ((2 * length512 ε x) * (ce * Real.log x) ^ e) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₀
          exact mul_le_mul hBcast hHnpow (by positivity) (by linarith)
      _ = (2 * C₀ * ce ^ e) * length512 ε x * (Real.log x) ^ e := by
          rw [mul_pow]; ring
      _ ≤ (Real.log x) * length512 ε x * (Real.log x) ^ e := by
          have h1 : (0 : ℝ) ≤ length512 ε x * (Real.log x) ^ e := by positivity
          nlinarith
      _ = length512 ε x * (Real.log x) ^ (e + 1) := by ring
      _ ≤ max 1 C₀ * length512 ε x * Real.log x ^ ((e + 1 : ℕ) : ℝ) := by
          have h1 : (1 : ℝ) ≤ max 1 C₀ := le_max_left _ _
          have h2 : (Real.log x) ^ (e + 1) = Real.log x ^ ((e + 1 : ℕ) : ℝ) :=
            (Real.rpow_natCast _ _).symm
          rw [h2]
          rw [mul_assoc]
          exact le_mul_of_one_le_left (by positivity) h1
  · have hzero : ∀ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ = 0 := by
      intro m _
      have hB0 : (0 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) ^ B :=
        Real.rpow_nonneg (by positivity) _
      have hprod : C₀ * ((m.divisors.card : ℕ) : ℝ) ^ B ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC₀ hB0
      have hle : ‖b m‖ ≤ 0 := le_trans (hb m) hprod
      exact le_antisymm hle (norm_nonneg _)
    rw [Finset.sum_eq_zero hzero]
    have h1 : (0 : ℝ) ≤ max 1 C₀ * length512 ε x * Real.log x ^ ((e + 1 : ℕ) : ℝ) := by
      have h2 : (0 : ℝ) ≤ Real.log x ^ ((e + 1 : ℕ) : ℝ) := Real.rpow_nonneg hlog0 _
      have h3 : (0 : ℝ) ≤ max 1 C₀ := le_trans zero_le_one (le_max_left _ _)
      positivity
    linarith

/-- LEAF. Replacement at a single frequency.  Assuming the prefix distribution of
b against every character of a small modulus, the error made by replacing the
actual short polynomial by its principal model at one even frequency is at most a
logarithmic saving times the mass of the short block.  The sum of squares over the
frequencies is not taken here. -/
theorem leaf_short_prefix_replacement561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℝ → ℕ → ℂ) (u v : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
          ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
              C * Y x * Real.log x ^ (-A)) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N ∈ frequencies512 ε x,
          ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ≤
            C * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- LEAF. Threshold step.  For small enough ε the block length is at least one, the
logarithm of x exceeds one, and the frequency height is at least one, from some
point onwards.  This produces the positive ε cut of the conclusion. -/
theorem leaf_short_length_bounds561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      1 ≤ length512 ε x ∧ 1 < Real.log x ∧
        1 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  refine ⟨1, one_pos, fun ε hε _hε1 => ⟨3, fun x hx => ?_⟩⟩
  have hx3 : (3 : ℝ) ≤ x := hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hcpos : (0 : ℝ) ≤ (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) := by
    have h1 : (0 : ℝ) < 11 / 20 + ε := by linarith
    have h2 : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5 : ℝ) := by norm_num
    exact (mul_pos h1 h2).le
  refine ⟨?_, ?_, ?_⟩
  · rw [length512]
    exact Real.one_le_rpow hx1 (by linarith)
  · exact (Real.lt_log_iff_exp_lt (x := 1) (y := x) hx0).mpr
      (lt_of_lt_of_le Real.exp_one_lt_three hx3)
  · exact Real.one_le_rpow hx1 hcpos

/-- The short coefficient replacement step, assembled from the frequency count, the
short block mass, the replacement at a single frequency and the elementary
thresholds.  CONDITIONAL ON those four separate inputs. -/
theorem leaf_short_coefficient561_split :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℝ → ℕ → ℂ) (u v : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
      (∃ C : ℝ, ∀ x k, ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
          ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
              C * Y x * Real.log x ^ (-A)) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          shortReplacementError561 ε D x (b x) u v ≤ C * scale512 ε A x := by
  intro B
  obtain ⟨εp, hεp, hpre⟩ := leaf_short_prefix_replacement561
  obtain ⟨εl, hεl, hlen⟩ := leaf_short_length_bounds561
  refine ⟨min εp εl, lt_min hεp hεl, ?_⟩
  intro ε hε hεlt b u v
  dsimp only
  intro hcoef hdist A hA
  obtain ⟨C₀, hC₀⟩ := hcoef
  obtain ⟨K, M, hK, hM, hmass⟩ := leaf_short_block_mass561 B C₀
  obtain ⟨Kc, hcard⟩ := leaf_short_frequency_card561 ε hε
  obtain ⟨Xlen, hXlen⟩ := hlen ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
  obtain ⟨Xmass, hXmass⟩ := hmass ε hε
  obtain ⟨Dp, hDp⟩ :=
    hpre ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)) b u v hdist (A + 14 + M) (by linarith)
  refine ⟨Dp, fun D hD => ?_⟩
  obtain ⟨Cpre, hCpre⟩ := hDp D hD
  let P : ℝ := |Cpre| * K
  let C : ℝ := max (max (max (max Kc Xmass) Cpre) (max Xlen 3)) (2 * P ^ 2)
  refine ⟨C, fun x hx => ?_⟩
  have h1 : Kc ≤ max Kc Xmass := le_max_left _ _
  have h2 : max Kc Xmass ≤ max (max Kc Xmass) Cpre := le_max_left _ _
  have h3 : max (max Kc Xmass) Cpre ≤ max (max (max Kc Xmass) Cpre) (max Xlen 3) :=
    le_max_left _ _
  have h4 : max (max (max Kc Xmass) Cpre) (max Xlen 3) ≤ C := le_max_left _ _
  have hxKc : Kc ≤ x := le_trans (le_trans (le_trans h1 h2) h3) (le_trans h4 hx)
  have hXm1 : Xmass ≤ max Kc Xmass := le_max_right _ _
  have hxXm : Xmass ≤ x := le_trans (le_trans (le_trans hXm1 h2) h3) (le_trans h4 hx)
  have hCp1 : Cpre ≤ max (max Kc Xmass) Cpre := le_max_right _ _
  have hxCp : Cpre ≤ x := le_trans (le_trans (le_trans hCp1 h3) h4) hx
  have hXl1 : Xlen ≤ max Xlen 3 := le_max_left _ _
  have hXl2 : max Xlen 3 ≤ max (max (max Kc Xmass) Cpre) (max Xlen 3) := le_max_right _ _
  have hxXl : Xlen ≤ x := le_trans (le_trans hXl1 hXl2) (le_trans h4 hx)
  have h31 : (3 : ℝ) ≤ max Xlen 3 := le_max_right _ _
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_trans h31 hXl2) (le_trans h4 hx)
  have hxP : 2 * P ^ 2 ≤ C := le_max_right _ _
  obtain ⟨hL1, hlog1, hH1⟩ := hXlen x hxXl
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := by linarith
  have hL0 : (0 : ℝ) ≤ length512 ε x := le_trans zero_le_one hL1
  let S : ℝ := ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖
  have hmassx : S ≤ K * length512 ε x * Real.log x ^ M :=
    hXmass x hxXm (b x) (fun k => hC₀ x k)
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hmul : Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M = Real.log x ^ (-A - 14) := by
    rw [← Real.rpow_add hlogpos]
    congr 1
    ring
  have hper : ∀ N ∈ frequencies512 ε x,
      ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ≤
        P * length512 ε x * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hCpre x hxCp N hN
    have hlogA : (0 : ℝ) ≤ Real.log x ^ (-(A + 14 + M)) := Real.rpow_nonneg hlog0 _
    have habs : (0 : ℝ) ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) :=
      mul_nonneg (abs_nonneg _) hlogA
    calc ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖
        ≤ Cpre * Real.log x ^ (-(A + 14 + M)) * S := h1
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) * S :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Cpre) hlogA) hS0
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) *
            (K * length512 ε x * Real.log x ^ M) :=
          mul_le_mul_of_nonneg_left hmassx habs
      _ = P * length512 ε x * (Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M) := by
          rw [show P = |Cpre| * K from rfl]
          ring
      _ = P * length512 ε x * Real.log x ^ (-A - 14) := by rw [hmul]
  have hsq : ∀ N ∈ frequencies512 ε x,
      ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ^ 2 ≤
        (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hper N hN
    have hq0 : (0 : ℝ) ≤ Real.log x ^ (-A - 14) := Real.rpow_nonneg hlog0 _
    have hq1 : Real.log x ^ (-A - 14) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ^ 2
        ≤ (P * length512 ε x * Real.log x ^ (-A - 14)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (P ^ 2 * length512 ε x ^ 2) * (Real.log x ^ (-A - 14)) ^ 2 := by ring
      _ ≤ (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [hq0, hq1]
  have hsum1 : shortReplacementError561 ε D x (b x) u v ≤
      ∑ N ∈ frequencies512 ε x, (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    unfold shortReplacementError561
    exact Finset.sum_le_sum hsq
  have hconst : (∑ N ∈ frequencies512 ε x,
        (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) =
      ((frequencies512 ε x).card : ℝ) *
        ((P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardx := hcard x hxKc
  have hbase0 : (0 : ℝ) ≤ (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) :=
    mul_nonneg (mul_nonneg (sq_nonneg P) (sq_nonneg _)) (Real.rpow_nonneg hlog0 _)
  calc shortReplacementError561 ε D x (b x) u v
      ≤ ∑ N ∈ frequencies512 ε x, (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) :=
        hsum1
    _ = ((frequencies512 ε x).card : ℝ) *
          ((P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) := hconst
    _ ≤ (2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) *
          ((P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) :=
        mul_le_mul_of_nonneg_right hcardx hbase0
    _ = (2 * P ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
            Real.log x ^ (-A - 14)) := by ring
    _ ≤ (2 * P ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
            Real.log x ^ (-A - 7)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (Real.rpow_nonneg hx0 _) (sq_nonneg _))
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (2 * P ^ 2) * scale512 ε A x := by rw [scale512]
    _ ≤ C * scale512 ε A x :=
        mul_le_mul_of_nonneg_right hxP (by
          rw [scale512]
          exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0 _) (sq_nonneg _))
            (Real.rpow_nonneg hlog0 _))

end LeanLab.BHP1997.Decomp561n
