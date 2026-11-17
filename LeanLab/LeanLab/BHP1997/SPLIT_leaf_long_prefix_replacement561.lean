/-
Independent split of the single frequency replacement of the long polynomial by its
principal model.  The major arc integral is written as the sum of its Farey arcs, the
modulus cutoff of the major arcs is dominated by the Farey order, a single arc is
compared with the corresponding model term at a cost of a logarithmic saving times the
window width, and the resulting modulus sum is collected with the elementary harmonic
bound.  The main term of each arc is the mass of the short block.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_coefficient561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- A fixed power of the logarithm is eventually below any fixed positive power of `x`. -/
private lemma eventually_log_pow_le_rpow561 {k C c : ℝ} (hk : 0 ≤ k) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop, C * Real.log x ^ k ≤ x ^ c := by
  set r : ℝ := c / (2 * (k + 1)) with hr
  have hk1 : 0 < k + 1 := by linarith
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrk : r * k < c := by
    rw [hr, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, C / r ^ k ≤ x ^ (c - r * k) :=
    (tendsto_rpow_atTop (by linarith : 0 < c - r * k)).eventually_ge_atTop (C / r ^ k)
  filter_upwards [h1, h2] with x hx1 hx2
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log x ≤ x ^ r / r := Real.log_le_rpow_div hx0.le hrpos
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hdiv : (0 : ℝ) ≤ x ^ r / r := by positivity
  have hpow : Real.log x ^ k ≤ (x ^ r / r) ^ k := Real.rpow_le_rpow hlog0 hlog hk
  have hstep : (x ^ r / r) ^ k = x ^ (r * k) * r ^ (-k) := by
    have hxr : (0 : ℝ) ≤ x ^ r := Real.rpow_nonneg hx0.le r
    rw [Real.div_rpow hxr hrpos.le, Real.rpow_mul hx0.le, Real.rpow_neg hrpos.le]
    field_simp
  have hmul : x ^ (c - r * k) * x ^ (r * k) = x ^ c := by
    rw [← Real.rpow_add hx0]
    ring_nf
  calc C * Real.log x ^ k ≤ C * ((x ^ r / r) ^ k) := by
        exact mul_le_mul_of_nonneg_left hpow hC.le
    _ = C * (x ^ (r * k) * r ^ (-k)) := by rw [hstep]
    _ = (C / r ^ k) * x ^ (r * k) := by
        rw [Real.rpow_neg hrpos.le]
        field_simp
    _ ≤ x ^ (c - r * k) * x ^ (r * k) := by
        refine mul_le_mul_of_nonneg_right hx2 (Real.rpow_nonneg hx0.le _)
    _ = x ^ c := hmul

/-- The explicit thresholds needed for the arc decomposition: `x` is large enough that
a fixed power of `log x` is dominated by any fixed positive power of `x`, uniformly in
the two free parameters. -/
private lemma exists_threshold561 (ε D : ℝ) (hc : 0 < 11 / 20 + ε) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (1 : ℝ) ≤ Real.log x ∧
      (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) ∧
      4 * Real.log x ^ (8 * D) ≤ length512 ε x := by
  have he : (0 : ℝ) < 1 / 16 - 1 / 10 ^ 5 := by norm_num
  have h1e : (0 : ℝ) < 1 - (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have h2D : (0 : ℝ) ≤ 2 * D := by linarith
  have h4D : (0 : ℝ) ≤ 4 * D := by linarith
  have h8D : (0 : ℝ) ≤ 8 * D := by linarith
  have hce : (0 : ℝ) < (11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) := mul_pos hc he
  have hc1 : (0 : ℝ) < (11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5)) := mul_pos hc h1e
  have ev2 : ∀ᶠ x : ℝ in Filter.atTop,
      (4 : ℝ) ≤ x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) :=
    (tendsto_rpow_atTop hce).eventually_ge_atTop 4
  have ev3 : ∀ᶠ x : ℝ in Filter.atTop,
      8 * Real.log x ^ (2 * D) ≤ x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) :=
    eventually_log_pow_le_rpow561 h2D (by norm_num) hce
  have ev4 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (4 * D) ≤ x ^ ((11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5))) := by
    filter_upwards [eventually_log_pow_le_rpow561 (C := 1) h4D (by norm_num) hc1] with x hx
    simpa using hx
  have ev6 : ∀ᶠ x : ℝ in Filter.atTop,
      4 * Real.log x ^ (8 * D) ≤ x ^ (11 / 20 + ε) :=
    eventually_log_pow_le_rpow561 h8D (by norm_num) hc
  have all : ∀ᶠ x : ℝ in Filter.atTop,
      (1 : ℝ) ≤ Real.log x ∧
      (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) ∧
      Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) ∧
      4 * Real.log x ^ (8 * D) ≤ length512 ε x := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 2), ev2, ev3, ev4, ev6]
      with x hxe h2 h3 h4 h6
    have hxe0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 2) hxe
    have hlen : ∀ e : ℝ, length512 ε x ^ e = x ^ ((11 / 20 + ε) * e) := by
      intro e
      unfold length512
      exact (Real.rpow_mul hxe0.le (11 / 20 + ε) e).symm
    have hL : length512 ε x = x ^ (11 / 20 + ε) := by
      unfold length512; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h := Real.log_le_log (Real.exp_pos 2) hxe
      rw [Real.log_exp] at h
      linarith
    · have heq : x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) =
          length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
        (hlen (1 / 16 - 1 / 10 ^ 5 : ℝ)).symm
      rw [heq] at h2
      exact h2
    · have heq : x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5)) =
          length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
        (hlen (1 / 16 - 1 / 10 ^ 5 : ℝ)).symm
      rw [heq] at h3
      exact h3
    · have heq : x ^ ((11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5))) =
          length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) :=
        (hlen (1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)).symm
      rw [heq] at h4
      exact h4
    · rw [hL]
      exact h6
  rw [Filter.eventually_atTop] at all
  obtain ⟨X, hX⟩ := all
  exact ⟨X, hX⟩

/-- The Farey order of the major arcs is close to the `(1/16 - 1e-5)` power of the block
length. -/
private lemma order_bounds561 {ε x : ℝ} (hlen0 : 0 ≤ length512 ε x)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ))) :
    length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 ≤ (order512 ε x : ℝ) ∧
    (order512 ε x : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2 := by
  have hkey : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) =
      length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) := by
    rw [← Real.rpow_mul hlen0]
    norm_num
  have hfl : (order512 ε x : ℝ) =
      ⌊length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2⌋₊ := by
    unfold order512
    rw [hkey]
  constructor
  · rw [hfl]
    have h1 : length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2 - 1 <
        (⌊length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2)
      linarith
    nlinarith
  · rw [hfl]
    exact Nat.floor_le (by positivity)

/-- The modulus cutoff and its basic bound. -/
private lemma Q_facts561 {D x : ℝ} (hlog1 : 1 ≤ Real.log x) (hD : 0 ≤ D) :
    1 ≤ ⌊Real.log x ^ (2 * D)⌋₊ ∧
      ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ Real.log x ^ (2 * D) := by
  refine ⟨Nat.floor_pos.mpr (Real.one_le_rpow hlog1 (by linarith)),
    Nat.floor_le (Real.rpow_nonneg (by linarith) _)⟩

/-- Every reduced Farey arc of the major arcs lies inside the complete period; this is
where the block length dominates the arc width and the Farey order. -/
private lemma arc_containment561 {ε D x w : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x)
    {Q q : ℕ} (hQ1 : 1 ≤ Q) (hQle : (Q : ℝ) ≤ Real.log x ^ (2 * D))
    (hq1 : 1 ≤ q) (hqQ : q ≤ Q)
    (hw : w = Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
    {r : ℕ} (hr1 : 1 ≤ r) (hrq : r ≤ q) :
    Set.Icc ((r : ℝ) / (q : ℝ) - w) ((r : ℝ) / (q : ℝ) + w) ⊆
      Set.Ioc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hlen0 : (0 : ℝ) ≤ length512 ε x := le_of_lt hlenpos
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have he : (0 : ℝ) < 1 / 16 - 1 / 10 ^ 5 := by norm_num
  obtain ⟨hordlo, hordub⟩ := order_bounds561 hlen0 h4
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    linarith
  have hQle' : (Q : ℝ) ≤ Real.log x ^ (2 * D) := hQle
  have hqleQ : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hLepos : (0 : ℝ) < length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
    Real.rpow_pos_of_pos hlenpos _
  have hordpos : (0 : ℝ) < (order512 ε x : ℝ) := by linarith
  have h2Q : 2 * (Q : ℝ) ≤ (order512 ε x : ℝ) := by
    have h3 : 2 * Real.log x ^ (2 * D) ≤
        length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 := by linarith
    have h4' : 2 * (Q : ℝ) ≤ 2 * Real.log x ^ (2 * D) := by linarith
    linarith
  have hinv1 : 1 / (order512 ε x : ℝ) ≤ 1 / (2 * (Q : ℝ)) :=
    one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 2 * (Q : ℝ)) h2Q
  have hL4D : (0 : ℝ) < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos hLpos _
  have h6 : 4 * (Q : ℝ) * Real.log x ^ (4 * D) ≤ length512 ε x := by
    have hL68 : Real.log x ^ (6 * D) ≤ Real.log x ^ (8 * D) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have hmul : Real.log x ^ (2 * D) * Real.log x ^ (4 * D) = Real.log x ^ (6 * D) := by
      rw [← Real.rpow_add hLpos]; ring_nf
    have h2 : (Q : ℝ) * Real.log x ^ (4 * D) ≤
        Real.log x ^ (2 * D) * Real.log x ^ (4 * D) :=
      mul_le_mul_of_nonneg_right hQle' (le_of_lt hL4D)
    have h3 : (Q : ℝ) * Real.log x ^ (4 * D) ≤ Real.log x ^ (8 * D) := by
      rw [hmul] at h2; exact le_trans h2 hL68
    linarith
  have hwq : w ≤ 1 / (4 * (Q : ℝ)) := by
    rw [hw, div_le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * length512 ε x)
      (by positivity : (0 : ℝ) < 4 * (Q : ℝ))]
    have hqlen : length512 ε x ≤ (q : ℝ) * length512 ε x := by
      have h1 : (1 : ℝ) * length512 ε x ≤ (q : ℝ) * length512 ε x :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hq1 : (1 : ℝ) ≤ (q : ℝ)) (le_of_lt hlenpos)
      simpa using h1
    nlinarith [h6, hqlen]
  have hqinv : 1 / (Q : ℝ) ≤ 1 / (q : ℝ) :=
    one_div_le_one_div_of_le hqpos hqleQ
  have hfrac1 : 1 / (q : ℝ) ≤ (r : ℝ) / (q : ℝ) := by
    have h : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    exact div_le_div_of_nonneg_right h (le_of_lt hqpos)
  have hlow : 1 / (order512 ε x : ℝ) < (r : ℝ) / (q : ℝ) - w := by
    have hA : 1 / (2 * (Q : ℝ)) < 1 / (Q : ℝ) - 1 / (4 * (Q : ℝ)) := by
      have hQ0 : (0 : ℝ) < (Q : ℝ) := hQpos
      field_simp
      linarith
    have hC : 1 / (q : ℝ) - 1 / (4 * (Q : ℝ)) ≤ (r : ℝ) / (q : ℝ) - w := by linarith
    linarith
  have hfrac2 : (r : ℝ) / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqpos]
    exact_mod_cast hrq
  have hwsmall : w ≤ 1 / (order512 ε x : ℝ) := by
    rw [hw, div_le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * length512 ε x) hordpos]
    have hsplit : length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) *
        length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)) = length512 ε x := by
      rw [← Real.rpow_add hlenpos]
      norm_num
    have h1 : (order512 ε x : ℝ) * Real.log x ^ (4 * D) ≤ length512 ε x := by
      calc (order512 ε x : ℝ) * Real.log x ^ (4 * D)
          ≤ (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 2) * Real.log x ^ (4 * D) :=
            mul_le_mul_of_nonneg_right hordub (le_of_lt hL4D)
        _ = (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) * Real.log x ^ (4 * D)) / 2 := by
            ring
        _ ≤ (length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) *
              length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ))) / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hordhi (le_of_lt hLepos)
        _ = length512 ε x / 2 := by rw [hsplit]
        _ ≤ length512 ε x := by linarith
    have h2 : Real.log x ^ (4 * D) * (order512 ε x : ℝ) ≤ length512 ε x := by
      rw [mul_comm]; exact h1
    have hqlen : length512 ε x ≤ (q : ℝ) * length512 ε x := by
      have h1 : (1 : ℝ) * length512 ε x ≤ (q : ℝ) * length512 ε x :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hq1 : (1 : ℝ) ≤ (q : ℝ)) (le_of_lt hlenpos)
      simpa using h1
    nlinarith [h1, hqlen]
  intro t ht
  exact ⟨by linarith [ht.1, hlow], by linarith [ht.2, hfrac2, hwsmall]⟩

/-- Distinct reduced fractions are separated by the reciprocal of the product of their
moduli. -/
private lemma frac_separation561 {q q' r r' : ℕ} (hq1 : 1 ≤ q) (hq'1 : 1 ≤ q')
    (hcq : Nat.Coprime r q) (hcq' : Nat.Coprime r' q')
    (hne : (q, r) ≠ (q', r')) :
    1 / ((q : ℝ) * q') ≤ |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)| := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have hq'pos : (0 : ℝ) < (q' : ℝ) := by
    have h : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'1
    linarith
  have hq0 : q ≠ 0 := by omega
  set m : ℤ := (r : ℤ) * (q' : ℤ) - (r' : ℤ) * (q : ℤ) with hm
  have hcast : ((m : ℤ) : ℝ) = (r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ) := by
    simp only [hm, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hne_int : m ≠ 0 := by
    intro h0
    have h3 : (r : ℤ) * (q' : ℤ) = (r' : ℤ) * (q : ℤ) := by
      have := sub_eq_zero.mp h0
      exact this
    have h1' : r * q' = r' * q := by
      have h4 : ((r * q' : ℕ) : ℤ) = ((r' * q : ℕ) : ℤ) := by
        push_cast
        exact h3
      exact_mod_cast h4
    have hd1 : q ∣ q' := by
      have h : r * q' = q * r' := by rw [h1', mul_comm]
      exact hcq.symm.dvd_of_dvd_mul_left ⟨r', h⟩
    have hd2 : q' ∣ q := by
      have h : r' * q = q' * r := by rw [← h1', mul_comm]
      exact hcq'.symm.dvd_of_dvd_mul_left ⟨r, h⟩
    have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
    have hr : r = r' := by
      have h2 : r * q = r' * q := by rw [← hqq] at h1'; exact h1'
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) h2
    exact hne (by rw [hqq, hr])
  have hA : (1 : ℝ) ≤ |(r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)| := by
    have h1 : (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by
      have h2 := Int.one_le_abs hne_int
      exact_mod_cast h2
    have h2 : ((|m| : ℤ) : ℝ) = |((m : ℤ) : ℝ)| := by simp
    rw [h2] at h1
    rwa [hcast] at h1
  have hfrac : (r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ) =
      ((r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)) / ((q : ℝ) * (q' : ℝ)) := by
    field_simp
  have h1 : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤
      |(r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)| / ((q : ℝ) * (q' : ℝ)) :=
    div_le_div_of_nonneg_right hA (by positivity)
  have h2 : |(r : ℝ) * (q' : ℝ) - (r' : ℝ) * (q : ℝ)| / ((q : ℝ) * (q' : ℝ)) =
      |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)| := by
    rw [hfrac, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * (q' : ℝ))]
  exact le_trans h1 (le_of_eq h2)

/-- Two closed arcs around distinct fractions are disjoint as soon as their widths add up
to less than the separation of the fractions. -/
private lemma arcs_disjoint561 {L4D len : ℝ} (hL4D : 0 ≤ L4D) (hlenpos : 0 < len)
    {q q' : ℕ} (hqpos : (0 : ℝ) < (q : ℝ)) (hq'pos : (0 : ℝ) < (q' : ℝ))
    {r r' : ℕ}
    (hsep : 1 / ((q : ℝ) * q') ≤ |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)|)
    (hwidth : L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) < 1 / ((q : ℝ) * q')) :
    Disjoint
      (Set.Icc ((r : ℝ) / (q : ℝ) - L4D / ((q : ℝ) * len))
        ((r : ℝ) / (q : ℝ) + L4D / ((q : ℝ) * len)))
      (Set.Icc ((r' : ℝ) / (q' : ℝ) - L4D / ((q' : ℝ) * len))
        ((r' : ℝ) / (q' : ℝ) + L4D / ((q' : ℝ) * len))) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  have hA : (r' : ℝ) / (q' : ℝ) - (r : ℝ) / (q : ℝ) ≤
      L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) := by
    linarith [ht.2, ht'.1]
  have hB : (r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ) ≤
      L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) := by
    linarith [ht.1, ht'.2]
  have habs : |(r : ℝ) / (q : ℝ) - (r' : ℝ) / (q' : ℝ)| ≤
      L4D / ((q : ℝ) * len) + L4D / ((q' : ℝ) * len) :=
    abs_sub_le_iff.mpr ⟨hB, hA⟩
  linarith [hsep, hwidth, habs]

/-- The finite exponential polynomial is continuous (reproved here because
`Decomp512a` is not in the import closure of this file). -/
private lemma continuous_polynomial561 (S : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (fun t : ℝ => polynomial512 S c t) := by
  unfold polynomial512
  exact continuous_finsetSum S fun k hk => continuous_const.mul
    ((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp (AddCircle.continuous_mk' 1))

/-- The integrand is continuous. -/
private lemma continuous_integrand561 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => integrand512 ε x a b N t) := by
  unfold integrand512
  exact ((continuous_polynomial561 _ _).mul (continuous_polynomial561 _ _)).mul
    ((map_continuous (fourier (T := (1 : ℝ)) (-(N : ℤ)))).comp
      (AddCircle.continuous_mk' 1))

/-- On a single arc the integral equals the local integral in the variable of the arc. -/
private lemma arc_integral_shift561 (ε D x : ℝ) (a b : ℕ → ℂ) (N q r : ℕ) (hx1 : 1 < x) :
    (∫ t in Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
        integrand512 ε x a b N t)
      = ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
          (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
          integrand512 ε x a b N ((r : ℝ) / (q : ℝ) + s) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hw : (0 : ℝ) ≤ Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) := by
    have hL : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hl : (0 : ℝ) < length512 ε x := by
      unfold length512
      exact Real.rpow_pos_of_pos hx0 _
    have h1 : (0 : ℝ) < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos hL _
    have h2 : (0 : ℝ) ≤ ((q : ℝ)) := Nat.cast_nonneg q
    by_cases hq : q = 0
    · simp [hq]
    · have hqpos : (0 : ℝ) < (q : ℝ) := by
        have : (0:ℕ) < q := Nat.pos_of_ne_zero hq
        exact_mod_cast this
      positivity
  have hle : (r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) ≤
      (r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) := by
    linarith
  have h1 : (∫ t in Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
        integrand512 ε x a b N t)
      = ∫ t in ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))..
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
          integrand512 ε x a b N t := by
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc).trans
      (intervalIntegral.integral_of_le hle).symm
  rw [h1]
  exact (intervalIntegral.integral_comp_add_left (integrand512 ε x a b N)
    ((r : ℝ) / (q : ℝ))).symm

/-- The major arcs are exactly the union of the local Farey arcs of the reduced residues
of the moduli up to the logarithmic cutoff. -/
private lemma major512_eq_arcs561 {ε D x : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x) :
    major512 ε D x = ⋃ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hlen0 : (0 : ℝ) ≤ length512 ε x := le_of_lt hlenpos
  obtain ⟨hordlo, hordub⟩ := order_bounds561 hlen0 h4
  obtain ⟨hQ1, hQle⟩ := Q_facts561 hlog1 hD
  have hQord' : 2 * ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ (order512 ε x : ℝ) := by
    have h2 : 2 * Real.log x ^ (2 * D) ≤
        length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 := by linarith
    have h3 : 2 * ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ 2 * Real.log x ^ (2 * D) := by
      linarith
    linarith
  have hQleord : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ (order512 ε x : ℝ) := by linarith
  have hmin : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = ⌊Real.log x ^ (2 * D)⌋₊ :=
    min_eq_right (by exact_mod_cast hQleord)
  have hQpos : (0 : ℝ) < ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hQ1
    linarith
  unfold major512 period512
  rw [hmin]
  ext t
  constructor
  · rintro ⟨-, ht⟩
    simpa only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_filter] using ht
  · intro ht
    simp only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_filter] at ht
    obtain ⟨q, ⟨hq1, hqQ⟩, r, ⟨⟨hr1, hrq⟩, hrc⟩, htr⟩ := ht
    have hsub := arc_containment561 hx1 hlog1 hD h4 hQord hordhi hlenbig
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) (q := q) hQ1 hQle hq1 hqQ
      (w := Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) rfl hr1 hrq
    have h2 := hsub htr
    have h2' := Set.mem_Ioc.mp h2
    refine ⟨⟨h2'.1, h2'.2⟩, ?_⟩
    simp only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_filter]
    exact ⟨q, ⟨hq1, hqQ⟩, r, ⟨⟨hr1, hrq⟩, hrc⟩, htr⟩

/-- A single arc stays inside `[0, 2]`, hence the integrand is integrable on it. -/
private lemma arc_subset_Icc561 {ε D x : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x)
    {q : ℕ} (hq1 : 1 ≤ q) (hqQn : q ≤ ⌊Real.log x ^ (2 * D)⌋₊)
    {r : ℕ} (hr1 : 1 ≤ r) (hrq : r ≤ q) :
    Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
      ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) ⊆
      Set.Icc (0 : ℝ) 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hlen0 : (0 : ℝ) ≤ length512 ε x := le_of_lt hlenpos
  obtain ⟨hordlo, hordub⟩ := order_bounds561 hlen0 h4
  obtain ⟨hQ1, hQle⟩ := Q_facts561 hlog1 hD
  have hordpos : (0 : ℝ) < (order512 ε x : ℝ) := by
    have h1 : (0 : ℝ) < length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) :=
      Real.rpow_pos_of_pos hlenpos _
    linarith
  have hqQ' : (q : ℝ) ≤ ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hqQn
  have hsub := arc_containment561 hx1 hlog1 hD h4 hQord hordhi hlenbig
    (Q := ⌊Real.log x ^ (2 * D)⌋₊) (q := q) hQ1 hQle hq1 hqQn
    (w := Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) rfl hr1 hrq
  intro t ht
  have h1 := Set.mem_Ioc.mp (hsub ht)
  refine ⟨?_, ?_⟩
  · have h2 : (0 : ℝ) < 1 / (order512 ε x : ℝ) := by
      rw [one_div_pos]
      exact hordpos
    linarith [h1.1]
  · have h2 : 1 / (order512 ε x : ℝ) ≤ 1 := by
      rw [div_le_one hordpos]
      have h3 : (1 : ℝ) ≤ (order512 ε x : ℝ) := by linarith
      exact h3
    linarith [h1.2]

/-- Two arcs belonging to different moduli are disjoint. -/
private lemma arc_pair_disjoint561 {ε D x : ℝ} (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x)
    (hD : 0 ≤ D)
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x)
    {Q : ℕ} (hQle : (Q : ℝ) ≤ Real.log x ^ (2 * D)) (hQ1 : 1 ≤ Q)
    {q q' r r' : ℕ} (hq1 : 1 ≤ q) (hqQ : q ≤ Q) (hq'1 : 1 ≤ q') (hq'Q : q' ≤ Q)
    (hr1 : 1 ≤ r) (hrq : r ≤ q) (hr'1 : 1 ≤ r') (hr'q : r' ≤ q')
    (hrc : Nat.Coprime r q) (hr'c : Nat.Coprime r' q')
    (hne : (q, r) ≠ (q', r')) :
    Disjoint
      (Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))
      (Set.Icc ((r' : ℝ) / (q' : ℝ) - Real.log x ^ (4 * D) / ((q' : ℝ) * length512 ε x))
        ((r' : ℝ) / (q' : ℝ) + Real.log x ^ (4 * D) / ((q' : ℝ) * length512 ε x))) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlenpos : (0 : ℝ) < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos hx0 _
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hLnn : (0 : ℝ) ≤ Real.log x := le_of_lt hLpos
  have hL4D : (0 : ℝ) < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos hLpos _
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have hq'pos : (0 : ℝ) < (q' : ℝ) := by
    have h : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'1
    linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    linarith
  have hsep := frac_separation561 hq1 hq'1 hrc hr'c hne
  have hqq' : (q : ℝ) * (q' : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    have h2 : (q' : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq'Q
    nlinarith [hqpos, hq'pos, hQpos]
  -- `log ^ 8D` beats `log ^ 4D * Q ^ 2`
  have hL6 : Real.log x ^ (4 * D) * (Q : ℝ) ^ 2 ≤ Real.log x ^ (8 * D) := by
    have h68 : Real.log x ^ (6 * D) ≤ Real.log x ^ (8 * D) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have hQ2 : (Q : ℝ) ^ 2 ≤ Real.log x ^ (2 * D) * Real.log x ^ (2 * D) := by
      rw [pow_two]
      exact mul_le_mul hQle hQle (le_of_lt hQpos) (Real.rpow_nonneg hLnn _)
    have hm1 : Real.log x ^ (4 * D) * (Real.log x ^ (2 * D) * Real.log x ^ (2 * D))
        = Real.log x ^ (6 * D) * Real.log x ^ (2 * D) := by
      have e1 : Real.log x ^ (4 * D) * Real.log x ^ (2 * D) = Real.log x ^ (6 * D) := by
        rw [← Real.rpow_add hLpos]; ring_nf
      rw [← e1]; ring
    have e2 : Real.log x ^ (6 * D) * Real.log x ^ (2 * D) = Real.log x ^ (8 * D) := by
      rw [← Real.rpow_add hLpos]; ring_nf
    calc Real.log x ^ (4 * D) * (Q : ℝ) ^ 2
        ≤ Real.log x ^ (4 * D) * (Real.log x ^ (2 * D) * Real.log x ^ (2 * D)) :=
          mul_le_mul_of_nonneg_left hQ2 (le_of_lt hL4D)
      _ = Real.log x ^ (6 * D) * Real.log x ^ (2 * D) := hm1
      _ = Real.log x ^ (8 * D) := e2
  have hsmall : 2 * Real.log x ^ (4 * D) * ((q : ℝ) * (q' : ℝ)) < length512 ε x := by
    have h1 : 2 * Real.log x ^ (4 * D) * ((q : ℝ) * (q' : ℝ)) ≤
        2 * Real.log x ^ (4 * D) * (Q : ℝ) ^ 2 := by
      refine mul_le_mul_of_nonneg_left hqq' ?_
      linarith
    have h2 : 2 * Real.log x ^ (4 * D) * (Q : ℝ) ^ 2 ≤ 2 * Real.log x ^ (8 * D) := by
      linarith [hL6]
    have h3 : (0 : ℝ) < Real.log x ^ (8 * D) := Real.rpow_pos_of_pos hLpos _
    nlinarith [hlenbig, h3, h1, h2]
  refine arcs_disjoint561 (le_of_lt hL4D) hlenpos hqpos hq'pos hsep ?_
  have hqc : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hq'c : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'1
  have hw1 : Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) ≤
      Real.log x ^ (4 * D) / length512 ε x := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * length512 ε x)
      (by positivity : (0 : ℝ) < length512 ε x)]
    have h : length512 ε x ≤ (q : ℝ) * length512 ε x := by
      have h' := mul_le_mul_of_nonneg_right hqc (le_of_lt hlenpos)
      simpa using h'
    exact mul_le_mul_of_nonneg_left h hL4D.le
  have hw2 : Real.log x ^ (4 * D) / ((q' : ℝ) * length512 ε x) ≤
      Real.log x ^ (4 * D) / length512 ε x := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (q' : ℝ) * length512 ε x)
      (by positivity : (0 : ℝ) < length512 ε x)]
    have h : length512 ε x ≤ (q' : ℝ) * length512 ε x := by
      have h' := mul_le_mul_of_nonneg_right hq'c (le_of_lt hlenpos)
      simpa using h'
    exact mul_le_mul_of_nonneg_left h hL4D.le
  have hmain : 2 * (Real.log x ^ (4 * D) / length512 ε x) < 1 / ((q : ℝ) * (q' : ℝ)) := by
    have h1 : 2 * (Real.log x ^ (4 * D) / length512 ε x)
        = 2 * Real.log x ^ (4 * D) / length512 ε x := by ring
    rw [h1]
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < length512 ε x)
      (by positivity : (0 : ℝ) < (q : ℝ) * (q' : ℝ))]
    linarith [hsmall]
  linarith [hw1, hw2, hmain]

/-- The major-arc integral is the sum of the local arc integrals. -/
private lemma integral_major512_arcs561 (ε D x : ℝ) (a b : ℝ → ℕ → ℂ) (N : ℕ)
    (hx1 : 1 < x) (hlog1 : 1 ≤ Real.log x) (hD : 0 ≤ D)
    (h4 : (4 : ℝ) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hQord : 8 * Real.log x ^ (2 * D) ≤ length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)))
    (hordhi : Real.log x ^ (4 * D) ≤ length512 ε x ^ ((1 - (1 / 16 - 1 / 10 ^ 5) : ℝ)))
    (hlenbig : 4 * Real.log x ^ (8 * D) ≤ length512 ε x) :
    (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
              (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  rw [major512_eq_arcs561 hx1 hlog1 hD h4 hQord hordhi hlenbig]
  have hcont := continuous_integrand561 ε x (a x) (b x) N
  have hbig : MeasureTheory.IntegrableOn (integrand512 ε x (a x) (b x) N) (Set.Icc (0 : ℝ) 2) :=
    hcont.integrableOn_Icc
  obtain ⟨hQ1, hQle⟩ := Q_facts561 hlog1 hD
  have hfin : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, MeasurableSet
      (⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro q hq
    exact Finset.measurableSet_biUnion _ (fun r hr => measurableSet_Icc)
  have hint : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      MeasureTheory.IntegrableOn (integrand512 ε x (a x) (b x) N)
        (⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
            ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro q hq
    refine hbig.mono_set ?_
    intro t ht
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_Icc] at ht
    obtain ⟨r, ⟨⟨hr1, hrq⟩, hrc⟩, htr⟩ := ht
    exact arc_subset_Icc561 hx1 hlog1 hD h4 hQord hordhi hlenbig
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2 hr1 hrq htr
  have hdisj : ((Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊ : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Disjoint
        (fun q => ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
            ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))) := by
    intro q hq q' hq' hne
    refine Set.disjoint_left.mpr ?_
    intro t ht ht'
    simp only [Set.mem_iUnion] at ht ht'
    obtain ⟨r, hr, htr⟩ := ht
    obtain ⟨r', hr', htr'⟩ := ht'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr hr'
    exact (Set.disjoint_left.mp (arc_pair_disjoint561 hx1 hlog1 hD hlenbig
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) hQle hQ1
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      (Finset.mem_Icc.mp hq').1 (Finset.mem_Icc.mp hq').2
      hr.1.1 hr.1.2 hr'.1.1 hr'.1.2 hr.2 hr'.2
      (by rintro ⟨rfl, rfl⟩; exact hne rfl))) htr htr'
  rw [MeasureTheory.integral_biUnion_finset (Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊) hfin hdisj hint]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hfin' : ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), MeasurableSet
      (Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
        ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro r hr
    exact measurableSet_Icc
  have hint' : ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      MeasureTheory.IntegrableOn (integrand512 ε x (a x) (b x) N)
        (Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))) := by
    intro r hr
    refine hbig.mono_set ?_
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    exact arc_subset_Icc561 hx1 hlog1 hD h4 hQord hordhi hlenbig
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2 hr.1.1 hr.1.2 ht
  have hdisj' : (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Disjoint
        (fun r => Set.Icc ((r : ℝ) / (q : ℝ) - Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x))
          ((r : ℝ) / (q : ℝ) + Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))) := by
    intro r hr r' hr' hne
    obtain ⟨hrI, hrc⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr'I, hr'c⟩ := Finset.mem_filter.mp hr'
    obtain ⟨hr1, hrq⟩ := Finset.mem_Icc.mp hrI
    obtain ⟨hr'1, hr'q⟩ := Finset.mem_Icc.mp hr'I
    exact arc_pair_disjoint561 hx1 hlog1 hD hlenbig
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) hQle hQ1
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      hr1 hrq hr'1 hr'q hrc hr'c
      (by rintro ⟨rfl, rfl⟩; exact hne rfl)
  rw [MeasureTheory.integral_biUnion_finset ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
    hfin' hdisj' hint']
  exact Finset.sum_congr rfl (fun r hr => arc_integral_shift561 ε D x (a x) (b x) N q r hx1)

/-- LEAF. Arc decomposition step.  The integrand is a finite sum of characters of the
circle, hence one periodic; the Farey arcs of the major arcs are eventually pairwise
disjoint, of width below the separation of neighbouring fractions with that denominator
cut, and every arc that leaves the fundamental period of the circle re-enters it shifted
by one.  Consequently the integral over the major arcs is the double sum over the
moduli and the reduced residues of the integral over the symmetric local arc around the
centre of that arc, in the local variable of the arc.  No distribution hypothesis and no
coefficient information is used. -/
theorem leaf_long_arc_decomposition561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (N : ℕ),
      (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
        ∑ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by

  have hexp2 : (1 : ℝ) < Real.exp 2 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  by_cases hc : (0 : ℝ) < 11 / 20 + ε
  · by_cases hD : (0 : ℝ) ≤ D
    · obtain ⟨X, hX⟩ := exists_threshold561 ε D hc hD
      refine ⟨max X (Real.exp 2) + 1, ?_⟩
      intro x hx a b N
      have hXx : X ≤ x := by
        have h0 : X ≤ max X (Real.exp 2) := le_max_left _ _
        linarith
      have hexp : Real.exp 2 ≤ x := by
        have h0 : Real.exp 2 ≤ max X (Real.exp 2) := le_max_right _ _
        linarith
      obtain ⟨hlog1, h4, hQord, hordhi, hlenbig⟩ := hX x hXx
      have hx1 : 1 < x := lt_of_lt_of_le hexp2 hexp
      have hlen0 : (0 : ℝ) ≤ length512 ε x := by
        unfold length512
        exact Real.rpow_nonneg (by linarith) _
      have hQleord : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ (order512 ε x : ℝ) := by
        obtain ⟨hordlo, -⟩ := order_bounds561 hlen0 h4
        have h1 : 2 * Real.log x ^ (2 * D) ≤
            length512 ε x ^ ((1 / 16 - 1 / 10 ^ 5 : ℝ)) / 4 := by linarith
        have h2 : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ Real.log x ^ (2 * D) :=
          (Q_facts561 hlog1 hD).2
        linarith
      have hmin : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = ⌊Real.log x ^ (2 * D)⌋₊ :=
        min_eq_right (by exact_mod_cast hQleord)
      rw [hmin]
      exact integral_major512_arcs561 ε D x a b N hx1 hlog1 hD h4 hQord hordhi hlenbig
    · push Not at hD
      refine ⟨max 1 (Real.exp 2) + 1, ?_⟩
      intro x hx a b N
      have hexp : Real.exp 2 ≤ x := by
        have h0 : Real.exp 2 ≤ max 1 (Real.exp 2) := le_max_right _ _
        linarith
      have hlog : 1 < Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 2) hexp
        rw [Real.log_exp] at h
        linarith
      have hQ0 : ⌊Real.log x ^ (2 * D)⌋₊ = 0 := by
        refine Nat.floor_eq_zero.mpr ?_
        exact Real.rpow_lt_one_of_one_lt_of_neg hlog (by linarith)
      have hmin0 : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = 0 := by
        rw [hQ0, min_zero]
      rw [hmin0]
      simp [major512, hmin0]
  · push Not at hc
    refine ⟨max 1 (Real.exp 2) + 1, ?_⟩
    intro x hx a b N
    have hx1 : (1 : ℝ) ≤ x := by
      have h0 : (1 : ℝ) ≤ max 1 (Real.exp 2) := le_max_left _ _
      linarith
    have hlenle : length512 ε x ≤ 1 := by
      unfold length512
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 hc
    have hlen0 : (0 : ℝ) ≤ length512 ε x := by
      unfold length512
      exact Real.rpow_nonneg (by linarith) _
    have hdelta : (0 : ℝ) ≤ 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
    have hord0 : order512 ε x = 0 := by
      unfold order512
      have h2 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) ≤ 1 := by
        refine Real.rpow_le_one (Real.rpow_nonneg hlen0 _) ?_ (by norm_num)
        exact Real.rpow_le_one hlen0 hlenle hdelta
      have h1 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) / 2 < 1 := by
        linarith
      exact Nat.floor_eq_zero.mpr h1
    have hmin0 : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = 0 := by
      rw [hord0, zero_min]
    rw [hmin0]
    simp [major512, hmin0]

/-- LEAF. Order domination step.  The Farey order of the major arcs grows like the
square root of a positive power of the block length, while the modulus cutoff of the
major arcs is a fixed power of the logarithm; from some point on the order is at least
the cutoff, so that the union of arcs is taken over the full range of the model sum.
This is an elementary threshold on `x`, uniform in the arc parameter. -/
theorem leaf_long_order_domination561 (ε D : ℝ) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := by
  sorry

/-- LEAF. Single arc replacement step.  On one reduced arc of the major arcs, the
actual long polynomial may be replaced by its principal model: the character expansion
of the phase at the centre of the arc, the prefix distribution of the long coefficients
against the characters of that modulus, the rough support that makes the coefficients
coprime to the modulus, and the total variation of the weight coming from the short
polynomial.  The cost is an arbitrary logarithmic saving times the width of the arc
times the mass of the short block, and it is uniform in the modulus and in the reduced
residue.  The saving is charged at an exponent strictly larger than the one required
later, which is what makes the modulus sum converge. -/
theorem leaf_long_arc_model_replacement561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ C₀ : ℝ, ∀ x : ℝ, C₀ ≤ x → ∀ D : ℝ, 0 ≤ D →
        ∀ N ∈ frequencies512 ε x, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖(∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))‖ ≤
          C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- Summing a per-pair bound `K / q` over the reduced residues of every modulus up to
`Q`: the reduced residue count is at most `q`, so the double sum is at most `K * Q`. -/
private lemma norm_sum_diff_le561 {Q : ℕ} {S : ℕ → Finset ℕ} {F H : ℕ → ℕ → ℂ} {K : ℝ}
    (hK : ∀ q ∈ Finset.Icc 1 Q, ∀ r ∈ S q, ‖F q r - H q r‖ ≤ K / (q : ℝ))
    (hcard : ∀ q ∈ Finset.Icc 1 Q, (S q).card ≤ q) :
    ‖(∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ S q, F q r) -
        (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ S q, H q r)‖ ≤ max (K * (Q : ℝ)) 0 := by
  have hqpos : ∀ q ∈ Finset.Icc 1 Q, (0 : ℝ) < (q : ℝ) := by
    intro q hq
    have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have h2 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
    linarith
  rw [← Finset.sum_sub_distrib]
  rcases le_total K 0 with hK0 | hKpos
  · have hz : ∀ q ∈ Finset.Icc 1 Q, (∑ r ∈ S q, F q r) = (∑ r ∈ S q, H q r) := by
      intro q hq
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have h1 : ‖F q r - H q r‖ ≤ 0 := by
        refine le_trans (hK q hq r hr) ?_
        exact div_nonpos_of_nonpos_of_nonneg hK0 (le_of_lt (hqpos q hq))
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _)))
    have hz' : ∀ q ∈ Finset.Icc 1 Q, ((∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r)) = 0 := by
      intro q hq
      rw [hz q hq, sub_self]
    rw [Finset.sum_congr rfl hz']
    simp only [Finset.sum_const_zero, norm_zero]
    exact le_max_right _ _
  · have hstep : ∀ q ∈ Finset.Icc 1 Q,
        ‖(∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r)‖ ≤ (S q).card * (K / (q : ℝ)) := by
      intro q hq
      rw [← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ r ∈ S q, ‖F q r - H q r‖ ≤ ∑ r ∈ S q, K / (q : ℝ) :=
            Finset.sum_le_sum (fun r hr => hK q hq r hr)
        _ = (S q).card * (K / (q : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc ‖∑ q ∈ Finset.Icc 1 Q, ((∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r))‖
        ≤ ∑ q ∈ Finset.Icc 1 Q, ‖(∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, (S q).card * (K / (q : ℝ)) := Finset.sum_le_sum hstep
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * (K / (q : ℝ)) := by
            refine Finset.sum_le_sum (fun q hq => ?_)
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact_mod_cast hcard q hq
            · exact div_nonneg hKpos (le_of_lt (hqpos q hq))
      _ = ∑ _q ∈ Finset.Icc 1 Q, K := by
            refine Finset.sum_congr rfl (fun q hq => ?_)
            have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (hqpos q hq)
            field_simp
      _ = (Q : ℝ) * K := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ max (K * (Q : ℝ)) 0 := by
            rw [mul_comm]
            exact le_max_left _ _

/-- The scalar bookkeeping of the modulus summation: a per-arc saving
`log x ^ (-(A + 6D + 3))` multiplied by `log x ^ (2D)` moduli, `log x ^ (4D)` arc widths
and a block length at least one gives the required `log x ^ (-A)`. -/
private lemma scalar_bookkeeping561 {L len A C₀ M : ℝ} {Q : ℕ} {D : ℝ}
    (hL1 : 1 ≤ L) (hlen1 : 1 ≤ len) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hQ : (Q : ℝ) ≤ L ^ (2 * D)) :
    max (C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) 0
      ≤ max 1 C₀ * L ^ (-A) * M := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hlenpos : (0 : ℝ) < len := lt_of_lt_of_le zero_lt_one hlen1
  have hlnn : (0 : ℝ) ≤ L ^ (-A) := Real.rpow_nonneg hLpos.le _
  have hcore : L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) ≤ L ^ (-A) * M := by
    have hexp : ∀ p q : ℝ, L ^ p * L ^ q = L ^ (p + q) := fun p q => (Real.rpow_add hLpos p q).symm
    have hcomb : L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) * L ^ (2 * D)) =
        L ^ (-A) * L ^ (-(3 : ℝ)) := by
      rw [hexp (4 * D) (2 * D), hexp (-(A + 6 * D + 3)) (4 * D + 2 * D), hexp (-A) (-(3 : ℝ)),
        show -(A + 6 * D + 3) + (4 * D + 2 * D) = -A + -(3 : ℝ) by ring]
    have hstep1 : L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
        = (L ^ (-(A + 6 * D + 3)) * M) * ((L ^ (4 * D) / len) * (Q : ℝ)) := by ring
    have hstep2 : (L ^ (4 * D) / len) * (Q : ℝ) ≤ L ^ (4 * D) * L ^ (2 * D) / len := by
      calc (L ^ (4 * D) / len) * (Q : ℝ) ≤ (L ^ (4 * D) / len) * L ^ (2 * D) :=
            mul_le_mul_of_nonneg_left hQ (by positivity)
        _ = L ^ (4 * D) * L ^ (2 * D) / len := by ring
    have hKnn : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) * M := by
      have h1 : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) := Real.rpow_nonneg hLpos.le _
      positivity
    have hstep3 : (L ^ (-(A + 6 * D + 3)) * M) * (L ^ (4 * D) * L ^ (2 * D) / len)
        = L ^ (-A) * L ^ (-(3 : ℝ)) * M / len := by
      rw [← hcomb]
      ring
    have hstep4 : L ^ (-A) * L ^ (-(3 : ℝ)) * M / len ≤ L ^ (-A) * M := by
      have h3 : L ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
      have h4 : L ^ (-A) * L ^ (-(3 : ℝ)) * M ≤ L ^ (-A) * 1 * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        exact mul_le_mul_of_nonneg_left h3 hlnn
      have h5 : (0 : ℝ) ≤ L ^ (-A) * L ^ (-(3 : ℝ)) * M := by positivity
      calc L ^ (-A) * L ^ (-(3 : ℝ)) * M / len ≤ L ^ (-A) * L ^ (-(3 : ℝ)) * M :=
            div_le_self h5 hlen1
        _ ≤ L ^ (-A) * 1 * M := h4
        _ = L ^ (-A) * M := by ring
    calc L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
        = (L ^ (-(A + 6 * D + 3)) * M) * ((L ^ (4 * D) / len) * (Q : ℝ)) := hstep1
      _ ≤ (L ^ (-(A + 6 * D + 3)) * M) * (L ^ (4 * D) * L ^ (2 * D) / len) :=
            mul_le_mul_of_nonneg_left hstep2 hKnn
      _ = L ^ (-A) * L ^ (-(3 : ℝ)) * M / len := hstep3
      _ ≤ L ^ (-A) * M := hstep4
  have hXQ : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) := by
    have h2 : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) := Real.rpow_nonneg hLpos.le _
    have h3 : (0 : ℝ) ≤ L ^ (4 * D) / len :=
      div_nonneg (Real.rpow_nonneg hLpos.le _) hlenpos.le
    have h4 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
    have h6 : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M := by positivity
    exact mul_nonneg h6 h4
  have hsplit : C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
      = C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) := by ring
  rcases lt_trichotomy C₀ 0 with hC₀ | hC₀ | hC₀
  · have hKQ : C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) ≤ 0 := by
      calc C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
          = C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) := hsplit
        _ ≤ 0 * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) :=
              mul_le_mul_of_nonneg_right hC₀.le hXQ
        _ = 0 := by ring
    rw [max_eq_right hKQ]
    have hfin : (0 : ℝ) ≤ max 1 C₀ * L ^ (-A) * M := by
      have h1 : (0 : ℝ) ≤ max 1 C₀ := le_trans zero_le_one (le_max_left _ _)
      have h2 : (0 : ℝ) ≤ max 1 C₀ * L ^ (-A) := mul_nonneg h1 hlnn
      exact mul_nonneg h2 hM
    linarith
  · subst hC₀
    rw [max_eq_left zero_le_one]
    simp only [zero_mul, max_self, one_mul]
    exact mul_nonneg (Real.rpow_nonneg hLpos.le _) hM
  · have h1 : C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ))
        ≤ C₀ * (L ^ (-A) * M) := mul_le_mul_of_nonneg_left hcore hC₀.le
    have hprod : (0 : ℝ) ≤ L ^ (-A) * M := mul_nonneg hlnn hM
    have h2 : C₀ * (L ^ (-A) * M) ≤ max 1 C₀ * (L ^ (-A) * M) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hprod
    have h4 : C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ))
        = C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) := by ring
    have h5 : C₀ * (L ^ (-A) * M) = C₀ * L ^ (-A) * M := by ring
    have h6 : max 1 C₀ * (L ^ (-A) * M) = max 1 C₀ * L ^ (-A) * M := by ring
    have hKQnn : (0 : ℝ) ≤ C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) := by
      rw [hsplit]
      exact mul_nonneg hC₀.le hXQ
    rw [max_eq_left hKQnn]
    linarith [h1, h2, h4, h5, h6]

/-- LEAF. Modulus summation step.  If every single arc is within a logarithmic saving
times the width of the arc times the mass of the short block of its model term, then the
double sum over the moduli and the reduced residues is within a fixed constant times the
required saving times the mass of the short block.  There are at most one power of the
logarithm per unit of the arc parameter many moduli, the reduced residue count cancels
against the totient weight of the model, and the extra saving charged per arc pays for
both.  Elementary summation and power arithmetic only. -/
theorem leaf_long_model_summation561 (ε D : ℝ) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (u A C₀ : ℝ) (N : ℕ),
      0 < A →
      ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x →
      N ∈ frequencies512 ε x →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖(∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))‖ ≤
          C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) →
      ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          longPrincipal561 ε D x (b x) u N‖ ≤
        max 1 C₀ * Real.log x ^ (-A) *
          ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by

  by_cases hc : (0 : ℝ) < 11 / 20 + ε
  · refine ⟨max 1 (Real.exp 2) + 1, ?_⟩
    intro x hx a b u A C₀ N hA hord _hNfreq hhyp
    have hxe : Real.exp 2 ≤ x := by
      have h0 : Real.exp 2 ≤ max 1 (Real.exp 2) := le_max_right _ _
      linarith
    have hexp2 : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    have hx1' : (1 : ℝ) < x := lt_of_lt_of_le hexp2 hxe
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx1'
    have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1'
    have hL1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 2) hxe
      rw [Real.log_exp] at h
      linarith
    have hlen1 : (1 : ℝ) ≤ length512 ε x := by
      unfold length512
      exact Real.one_le_rpow hx1 (le_of_lt hc)
    have hlenpos : (0 : ℝ) < length512 ε x := lt_of_lt_of_le zero_lt_one hlen1
    have hQle : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ Real.log x ^ (2 * D) :=
      Nat.floor_le (Real.rpow_nonneg hLpos.le _)
    have hMnn : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
      Finset.sum_nonneg (fun m _ => norm_nonneg _)
    have hmin : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = ⌊Real.log x ^ (2 * D)⌋₊ :=
      min_eq_right hord
    have hQcard : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ q := by
      intro q hq
      have h1 : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ (Finset.Icc 1 q).card :=
        Finset.card_filter_le _ _
      have h2 : (Finset.Icc 1 q).card = q := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      omega
    have hKstep : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖(∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
              (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          ((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
              (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ)))‖ ≤
          (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
              (Real.log x ^ (4 * D) / length512 ε x) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) / (q : ℝ) := by
      intro q hq r hr
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq2 : q ≤ ⌊Real.log x ^ (2 * D)⌋₊ := (Finset.mem_Icc.mp hq).2
      have hqle : (q : ℝ) ≤ Real.log x ^ (2 * D) := by
        have h2 : (q : ℝ) ≤ ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hq2
        linarith
      have h1 := hhyp q hq1 hqle r hr
      refine le_trans h1 (le_of_eq ?_)
      have hq0 : (q : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        linarith
      have hlen0 : length512 ε x ≠ 0 := ne_of_gt hlenpos
      field_simp
    have hlp : longPrincipal561 ε D x (b x) u N =
        ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
              ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
                  (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
                polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
                polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                  ((r : ℝ) / q + s) *
                @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ)) := by
      unfold longPrincipal561
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [← mul_assoc, Finset.mul_sum]
    rw [hlp]
    refine le_trans (norm_sum_diff_le561 (S := fun q => (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
      (K := C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
        (Real.log x ^ (4 * D) / length512 ε x) *
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖)
      hKstep hQcard) ?_
    exact scalar_bookkeeping561 (L := Real.log x) (len := length512 ε x) (A := A) (C₀ := C₀)
      (M := ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖)
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) (D := D) hL1 hlen1 hMnn hD hQle
  · push Not at hc
    refine ⟨max 1 (Real.exp 2), ?_⟩
    intro x hx a b u A C₀ N hA hord _hNfreq _hhyp
    exfalso
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left (1 : ℝ) (Real.exp 2)) hx
    have hxe : Real.exp 2 ≤ x := le_trans (le_max_right (1 : ℝ) (Real.exp 2)) hx
    have hL1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 2) hxe
      rw [Real.log_exp] at h
      linarith
    have hlenle1 : length512 ε x ≤ 1 := by
      unfold length512
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 hc
    have hlen0 : (0 : ℝ) ≤ length512 ε x := by
      unfold length512
      exact Real.rpow_nonneg (le_trans zero_le_one hx1) _
    have hdelta : (0 : ℝ) ≤ 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
    have hord0 : order512 ε x = 0 := by
      unfold order512
      have h1 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
        refine Real.rpow_le_one (Real.rpow_nonneg hlen0 _) ?_ (by norm_num)
        exact Real.rpow_le_one hlen0 hlenle1 hdelta
      have h2 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2 < 1 := by
        linarith
      exact Nat.floor_eq_zero.mpr h2
    have hge : (1 : ℕ) ≤ ⌊Real.log x ^ (2 * D)⌋₊ := by
      refine Nat.floor_pos.mpr ?_
      exact Real.one_le_rpow hL1 (by linarith)
    rw [hord0] at hord
    omega

/-- The single frequency long coefficient replacement, assembled from the arc
decomposition, the order domination, the single arc replacement and the modulus
summation.  CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_prefix_replacement561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N ∈ frequencies512 ε x,
          ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
              longPrincipal561 ε D x (b x) u N‖ ≤
            C * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  obtain ⟨εR, hεR, hrep⟩ := leaf_long_arc_model_replacement561
  obtain ⟨εL, hεL, hlen⟩ := leaf_long_length_bounds561
  refine ⟨min εR εL, lt_min hεR hεL, ?_⟩
  intro ε hε hεlt a b u
  dsimp only
  intro hdist hrough A hA
  have hεR' : ε < εR := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεL' : ε < εL := lt_of_lt_of_le hεlt (min_le_right _ _)
  obtain ⟨Xl, hXl⟩ := hlen ε hε hεL'
  obtain ⟨C₀, hC₀⟩ := hrep ε hε hεR' a b u hdist hrough A hA
  refine ⟨0, fun D hD => ?_⟩
  have hD0 : (0 : ℝ) ≤ D := hD
  obtain ⟨Xa, hXa⟩ := leaf_long_arc_decomposition561 ε D
  obtain ⟨Xo, hXo⟩ := leaf_long_order_domination561 ε D hD0
  obtain ⟨Xs, hXs⟩ := leaf_long_model_summation561 ε D hD0
  refine ⟨max (max (max (max Xa Xo) (max Xl C₀)) Xs + 3) (max 1 C₀), fun x hx => ?_⟩
  intro N hN
  have hthr : max (max (max Xa Xo) (max Xl C₀)) Xs + 3 ≤ x := le_trans (le_max_left _ _) hx
  have hthr' : max (max (max Xa Xo) (max Xl C₀)) Xs ≤ x := by linarith
  have hM1 : max (max Xa Xo) (max Xl C₀) ≤ x := le_trans (le_max_left _ _) hthr'
  have hAB : max Xa Xo ≤ x := le_trans (le_max_left _ _) hM1
  have hxa : Xa ≤ x := le_trans (le_max_left _ _) hAB
  have hxo : Xo ≤ x := le_trans (le_max_right _ _) hAB
  have hCD : max Xl C₀ ≤ x := le_trans (le_max_right _ _) hM1
  have hxl : Xl ≤ x := le_trans (le_max_left _ _) hCD
  have hxp : C₀ ≤ x := le_trans (le_max_right _ _) hCD
  have hxs : Xs ≤ x := le_trans (le_max_right _ _) hthr'
  obtain ⟨hL1, hlog1, -⟩ := hXl x hxl
  have hord : ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := hXo x hxo
  have hid : (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
    rw [hXa x hxa a b N, min_eq_right hord]
  rw [hid]
  have hlogpos : 0 < Real.log x := by linarith
  have hM0 : (0 : ℝ) ≤
      ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    Finset.sum_nonneg (fun m _ => norm_nonneg _)
  refine le_trans (hXs x hxs a b u A C₀ N hA hord hN
    (fun q hq hqL r hr => hC₀ x hxp D hD0 N hN q hq hqL r hr)) ?_
  apply mul_le_mul_of_nonneg_right _ hM0
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (le_of_lt hlogpos) _)

end LeanLab.BHP1997.Decomp561n
