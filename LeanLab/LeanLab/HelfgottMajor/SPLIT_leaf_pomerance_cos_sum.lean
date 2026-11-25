import LeanLab.HelfgottMajor.SPLIT_leaf_odd_case_pomerance

/-!
Split of `leaf_pomerance_cos_sum`, the cosine sum bound in the proof of Pomerance,
Remarks on the Pólya-Vinogradov inequality, Integers 11A 2011, Article 19, section 4, odd case:
`sum_{m <= n} |cos m alpha - cos m beta| / m <= log n + gamma + log 2 + 3/n`.

Pomerance's ingredients:

* the harmonic bound, his display 3, `sum_{j <= n} 1/j < log n + gamma + 1/n`, proved here from
  Mathlib's `eulerMascheroniSeq_lt_eulerMascheroniConstant`;
* his Lemma 2, `C_n x > - log 2 - 2/n` for `C_n x = sum_{j <= n} cos (j x) / j`; its proof uses
  Young's theorem that for odd `n` the minimum of `C_n` sits at `x = pi`, left as the only LEAF,
  then the alternating sum bound and the even step, both proved here;
* the product formula `|cos a - cos b| = 2 |sin ((a+b)/2) sin ((a-b)/2)|` and Cauchy-Schwarz.
  Here Cauchy-Schwarz is replaced by the pointwise AM-GM form
  `|cos a - cos b| <= ((1 - cos (a+b)) + (1 - cos (a-b))) / 2`, which gives the same final bound,
  since each of Pomerance's two Cauchy-Schwarz factors is below the same quantity.

No definition is introduced. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real Finset

/-- LEAF: the core of Young 1913, as cited in Pomerance 2011 section 2, proof of Lemma 2,
reference 16, also Pólya-Szegő Part VI Problem 27: for odd `n`, at every interior critical point
`0 < x < pi` of `C_n x = sum_{j <= n} cos (j x) / j`, that is where
`C_n' x = - sum_{j <= n} sin (j x)` vanishes, the value is at least `C_n pi`.
Together with the calculus reduction `young_cos_min_odd_Icc` this is Young's statement that the
minimum of `C_n` on `0 <= x <= pi` sits at `x_n = pi` for odd `n`.
HARD: a genuine extremal problem for trigonometric polynomials. -/
theorem leaf_young_critical_value_odd (n : ℕ) (hn : Odd n) (x : ℝ) (hx0 : 0 < x) (hxpi : x < π)
    (hcrit : ∑ j ∈ Icc 1 n, sin (j * x) = 0) :
    ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) ≤ ∑ j ∈ Icc 1 n, cos (j * x) / (j : ℝ) := by
  sorry

/-- The derivative of `C_n x = sum_{j <= n} cos (j x) / j` is `- sum_{j <= n} sin (j x)`. -/
theorem hasDerivAt_cos_sum (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ j ∈ Icc 1 n, cos (j * t) / (j : ℝ))
      (∑ j ∈ Icc 1 n, -sin (j * x)) x := by
  have : ∀ j ∈ Icc 1 n, HasDerivAt (fun t : ℝ => cos (j * t) / (j : ℝ)) (-sin (j * x)) x := by
    intro j hj
    have hjpos : (j : ℝ) ≠ 0 := by
      have := (mem_Icc.1 hj).1; positivity
    have h1 : HasDerivAt (fun t : ℝ => (j : ℝ) * t) (j : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (j : ℝ)
    have h2 := (h1.cos).div_const (j : ℝ)
    convert h2 using 1
    field_simp
  simpa using HasDerivAt.fun_sum this

/-- Young's minimum on `0 <= x <= pi`, reduced to the critical values by calculus: the minimum of
the continuous `C_n` on the compact interval is at an endpoint or at an interior critical point.
At `x = 0` the value is the harmonic sum, at `x = pi` it is the alternating sum. -/
theorem young_cos_min_odd_Icc (n : ℕ) (hn : Odd n) (x : ℝ) (hx0 : 0 ≤ x) (hxpi : x ≤ π) :
    ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) ≤ ∑ j ∈ Icc 1 n, cos (j * x) / (j : ℝ) := by
  set f : ℝ → ℝ := fun t => ∑ j ∈ Icc 1 n, cos (j * t) / (j : ℝ) with hf
  have hcont : Continuous f := by
    rw [hf]; fun_prop
  obtain ⟨c, hc, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π)).exists_isMinOn
    (Set.nonempty_Icc.2 pi_pos.le) hcont.continuousOn
  have hfx : f c ≤ f x := hmin ⟨hx0, hxpi⟩
  suffices h : ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) ≤ f c from h.trans hfx
  obtain ⟨hc0, hcpi⟩ := hc
  rcases hc0.eq_or_lt with h0 | h0
  · -- `c = 0`: the harmonic sum
    rw [← h0, hf]
    refine sum_le_sum fun j hj => ?_
    simp only [mul_zero, cos_zero]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg j)
    rcases neg_one_pow_eq_or ℝ j with h | h <;> norm_num [h]
  rcases hcpi.eq_or_lt with hp | hp
  · -- `c = pi`: the alternating sum
    rw [hp, hf]
    refine le_of_eq (sum_congr rfl fun j _ => ?_)
    rw [cos_nat_mul_pi]
  · -- interior: a critical point
    have hloc : IsLocalMin f c :=
      hmin.isLocalMin (Icc_mem_nhds h0 hp)
    have hd := hloc.hasDerivAt_eq_zero (hasDerivAt_cos_sum n c)
    have hcrit : ∑ j ∈ Icc 1 n, sin (j * c) = 0 := by
      rw [sum_neg_distrib] at hd; linarith
    exact leaf_young_critical_value_odd n hn c h0 hp hcrit

/-- Pomerance 2011, proof of Lemma 2, first sentence: `C_n` is `2 pi` periodic and even, so
Young's minimum on `0 <= x <= pi` is the minimum over all real `x`. -/
theorem young_cos_min_odd (n : ℕ) (hn : Odd n) (x : ℝ) :
    ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) ≤ ∑ j ∈ Icc 1 n, cos (j * x) / (j : ℝ) := by
  set y := toIocMod two_pi_pos (-π) x with hy
  have hmem := toIocMod_mem_Ioc two_pi_pos (-π) x
  rw [← hy] at hmem
  obtain ⟨hy1, hy2⟩ := hmem
  have hxy : x = y + (toIocDiv two_pi_pos (-π) x : ℝ) * (2 * π) := by
    rw [hy, ← zsmul_eq_mul, toIocMod_add_toIocDiv_zsmul]
  have hcos : ∀ j : ℕ, cos ((j : ℝ) * x) = cos ((j : ℝ) * |y|) := by
    intro j
    rw [hxy, mul_add, ← mul_assoc, show ((j : ℝ) * (toIocDiv two_pi_pos (-π) x : ℝ)) =
      ((((j : ℤ) * toIocDiv two_pi_pos (-π) x : ℤ)) : ℝ) by push_cast; ring,
      cos_add_int_mul_two_pi]
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, cos_neg]
  have h := young_cos_min_odd_Icc n hn |y| (abs_nonneg y) (abs_le.2 ⟨by linarith, by linarith⟩)
  simpa only [hcos] using h

/-- The tail comparison `sum_{a < j <= b} 1/j <= log b - log a`, with strict inequality when
`a < b`, each term below `log j - log (j-1)`. Used for the alternating sum in Pomerance Lemma 2. -/
theorem sum_Ioc_inv_lt_log (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    ∑ j ∈ Ioc a b, 1 / (j : ℝ) < log b - log a := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Nat.Ioc_succ_singleton, sum_singleton]
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha
    have h1 : log ((a : ℝ) / (a + 1)) < (a : ℝ) / (a + 1) - 1 :=
      log_lt_sub_one_of_pos (by positivity) (by
        intro h; rw [div_eq_one_iff_eq (by positivity)] at h; linarith)
    rw [log_div hapos.ne' (by positivity)] at h1
    have h2 : (a : ℝ) / (a + 1) - 1 = -(1 / (a + 1)) := by field_simp; ring
    push_cast
    linarith
  | succ b hb ih =>
    rw [sum_Ioc_succ_top (by omega)]
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have h1 : log ((b : ℝ) / (b + 1)) < (b : ℝ) / (b + 1) - 1 :=
      log_lt_sub_one_of_pos (by positivity) (by
        intro h; rw [div_eq_one_iff_eq (by positivity)] at h; linarith)
    rw [log_div hbpos.ne' (by positivity)] at h1
    have h2 : (b : ℝ) / (b + 1) - 1 = -(1 / (b + 1)) := by field_simp; ring
    push_cast
    linarith

/-- The odd alternating sum identity, for `n = 2k+1`:
`sum_{j <= 2k+1} (-1)^j / j + 1/(2k+2) = - sum_{k+1 < j <= 2k+2} 1/j`. -/
theorem alt_sum_identity (k : ℕ) :
    ∑ j ∈ Icc 1 (2 * k + 1), (-1 : ℝ) ^ j / (j : ℝ) + 1 / (2 * (k : ℝ) + 2) =
      -∑ j ∈ Ioc (k + 1) (2 * k + 2), 1 / (j : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
    have e2 : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by ring
    rw [e1, e2, sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega),
      sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega)]
    have hc := sum_Ioc_consecutive (fun j : ℕ => 1 / (j : ℝ)) (show k + 1 ≤ k + 1 + 1 by omega)
      (show k + 1 + 1 ≤ 2 * k + 2 by omega)
    rw [Nat.Ioc_succ_singleton, sum_singleton] at hc
    have p1 : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
    have p2 : (-1 : ℝ) ^ (2 * k + 1 + 1 + 1) = -1 := by
      rw [show 2 * k + 1 + 1 + 1 = 2 * (k + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [p1, p2]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast at ih hc ⊢
    have q2 : 1 / (2 * ((k : ℝ) + 1) + 2) = 1 / ((2 * (k : ℝ) + 2 + 1 + 1)) := by ring_nf
    have q3 : 1 / (2 * (k : ℝ) + 2) = 1 / ((2 * (k : ℝ) + 1 + 1)) := by ring_nf
    have q4 : 1 / ((k : ℝ) + 1 + 1) = 2 * (1 / (2 * (k : ℝ) + 2 + 1 + 1)) := by
      field_simp; ring
    have q6 : (-1 : ℝ) / (2 * (k : ℝ) + 2 + 1) = -(1 / (2 * (k : ℝ) + 2 + 1)) := by ring
    have q5 : 1 / (2 * (k : ℝ) + 3 + 1) = 1 / ((2 * (k : ℝ) + 2 + 1 + 1)) := by ring_nf
    rw [q2]
    rw [q5]
    rw [q3] at ih
    linarith

/-- Pomerance 2011, proof of Lemma 2, odd case: the alternating sum satisfies
`sum_{j <= n} (-1)^j / j > - log 2 - 1/(n+1)` for odd `n`. -/
theorem alt_sum_gt (n : ℕ) (hn : Odd n) :
    -log 2 - 1 / ((n : ℝ) + 1) < ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ j / (j : ℝ) := by
  obtain ⟨k, rfl⟩ := hn
  have hid := alt_sum_identity k
  have hlt := sum_Ioc_inv_lt_log (k + 1) (2 * k + 2) (by omega) (by omega)
  have hlog : log ((2 * k + 2 : ℕ) : ℝ) - log ((k + 1 : ℕ) : ℝ) = log 2 := by
    rw [← log_div (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp
  push_cast at hid hlt hlog ⊢
  have : 1 / (((2 * (k : ℝ) + 1)) + 1) = 1 / (2 * (k : ℝ) + 2) := by ring_nf
  linarith

/-- Pomerance 2011, Lemma 2: for all real `x` and `n >= 1`,
`C_n x = sum_{j <= n} cos (j x) / j > - log 2 - 2/n`. -/
theorem pomerance_lemma2 (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    -log 2 - 2 / (n : ℝ) < ∑ j ∈ Icc 1 n, cos (j * x) / (j : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.even_or_odd n with he | ho
  · -- even case: peel off the last term
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 ∧ Odd m := by
      refine ⟨n - 1, by omega, ?_⟩
      rcases he with ⟨r, hr⟩
      exact ⟨r - 1, by omega⟩
    obtain ⟨rfl, hmo⟩ := hm
    rw [sum_Icc_succ_top (by omega)]
    have h1 := alt_sum_gt m hmo
    have h2 := young_cos_min_odd m hmo x
    have h3 : -1 ≤ cos (((m + 1 : ℕ) : ℝ) * x) := neg_one_le_cos _
    have h4 : -(1 / ((m + 1 : ℕ) : ℝ)) ≤ cos (((m + 1 : ℕ) : ℝ) * x) / ((m + 1 : ℕ) : ℝ) := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right h3 (by positivity)
    push_cast at h1 h4 ⊢
    have : 2 / ((m : ℝ) + 1) = 1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by ring
    linarith
  · have h1 := alt_sum_gt n ho
    have h2 := young_cos_min_odd n ho x
    have : 1 / ((n : ℝ) + 1) < 2 / (n : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hnpos]; linarith
    linarith

/-- Pomerance 2011, display 3: `sum_{j <= n} 1/j < log n + gamma + 1/n` for `n >= 1`. -/
theorem harmonic_sum_lt (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, 1 / (j : ℝ) < log n + eulerMascheroniConstant + 1 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have hH : (harmonic n : ℝ) = ∑ j ∈ Icc 1 n, 1 / (j : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  have h2 : log ((n : ℝ) + 1) - log n ≤ 1 / (n : ℝ) := by
    rw [← log_div (by positivity) hnpos.ne']
    have := log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  unfold eulerMascheroniSeq at h1
  linarith

/-- The pointwise AM-GM form of Pomerance's product step:
`|cos a - cos b| <= ((1 - cos (a+b)) + (1 - cos (a-b))) / 2`, which equals `1 - cos a cos b`. -/
theorem abs_cos_sub_cos_le (a b : ℝ) :
    |cos a - cos b| ≤ ((1 - cos (a + b)) + (1 - cos (a - b))) / 2 := by
  rw [cos_add, cos_sub]
  have ha1 := cos_le_one a
  have ha2 := neg_one_le_cos a
  have hb1 := cos_le_one b
  have hb2 := neg_one_le_cos b
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 ha1) (by linarith : (0 : ℝ) ≤ 1 + cos b),
    mul_nonneg (sub_nonneg.2 hb1) (by linarith : (0 : ℝ) ≤ 1 + cos a)]

/-- `leaf_pomerance_cos_sum` assembled from Pomerance's Lemma 2, display 3 and the product step;
the only remaining LEAF is `leaf_young_critical_value_odd`. -/
theorem leaf_pomerance_cos_sum_split (α β : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, |cos (m * α) - cos (m * β)| / (m : ℝ) <
      log N + eulerMascheroniConstant + log 2 + 3 / N := by
  have hle : ∑ m ∈ Finset.Icc 1 N, |cos (m * α) - cos (m * β)| / (m : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ) -
        (∑ m ∈ Icc 1 N, cos (m * (α + β)) / (m : ℝ) +
          ∑ m ∈ Icc 1 N, cos (m * (α - β)) / (m : ℝ)) / 2 := by
    rw [← sum_add_distrib, sum_div, ← sum_sub_distrib]
    refine sum_le_sum fun m hm => ?_
    have hmpos : (0 : ℝ) < m := by
      have := (mem_Icc.1 hm).1; exact_mod_cast this
    have h := abs_cos_sub_cos_le (m * α) (m * β)
    rw [show (m : ℝ) * α + m * β = m * (α + β) by ring,
      show (m : ℝ) * α - m * β = m * (α - β) by ring] at h
    have e : 1 / (m : ℝ) - (cos (m * (α + β)) / m + cos (m * (α - β)) / m) / 2 =
        ((1 - cos (m * (α + β))) + (1 - cos (m * (α - β)))) / 2 / m := by
      field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_right h hmpos.le
  have hH := harmonic_sum_lt N hN
  have hA := pomerance_lemma2 N hN (α + β)
  have hB := pomerance_lemma2 N hN (α - β)
  have e3 : 3 / (N : ℝ) = 1 / N + 2 / N := by ring
  linarith

end LeanLab.HelfgottMajor.PolyaVinogradov123
