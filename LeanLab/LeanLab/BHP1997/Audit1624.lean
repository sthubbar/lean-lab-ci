/-
P0069, pages 3, 11, 12, 51, 52 and 53. Audit for unit U-1624.
Part 1. Condition iii of Theorem 2, display 1.8, forces the two halves of J to carry equal mass
up to every logarithmic power. A coefficient that follows the density 1 / log m does not do this.
Part 2. The transfer from a variable center to a constant center, for a general rescaling factor.
Part 3. Each leaf of the two SPLIT_hybrid files follows from its sealed target.
This refutes a raw candidate only. It does not refute Theorem 2, Theorem 1 or either existential
weight leaf of DecompC165d.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165
import LeanLab.BHP1997.MeanSquareC165
import LeanLab.BHP1997.Decomp387e

namespace LeanLab.BHP1997.Audit1624
open Classical Complex DecompC165b

/-- Page 3, the parameter Y of the short interval J. -/
noncomputable def shortY (ε x : ℝ) : ℝ := x ^ (11 / 20 + ε)
/-- The left end of the integer interval J. -/
noncomputable def lowEnd (ε x : ℝ) : ℕ := ⌊shortY ε x⌋₊
/-- The right end of the integer interval J. -/
noncomputable def highEnd (ε x : ℝ) : ℕ := ⌊2 * shortY ε x⌋₊
/-- The integer midpoint of J. -/
noncomputable def midEnd (ε x : ℝ) : ℕ := lowEnd ε x + (highEnd ε x - lowEnd ε x) / 2

/-- Finite step. Two centered prefix bounds control the difference of the two half masses. -/
theorem half_balance_finite (c : ℕ → ℝ) (d R : ℝ) {L U : ℕ} (hLU : L ≤ U)
    (h1 : |∑ m ∈ Finset.Ioc L (L + (U - L) / 2), (c m - d)| ≤ R)
    (h2 : |∑ m ∈ Finset.Ioc L U, (c m - d)| ≤ R) :
    |(∑ m ∈ Finset.Ioc (L + (U - L) / 2) U, c m) -
        ∑ m ∈ Finset.Ioc L (L + (U - L) / 2), c m| ≤ 3 * R + |d| := by
  set M := L + (U - L) / 2 with hM
  have hLM : L ≤ M := by omega
  have hMU : M ≤ U := by omega
  have hsplit := Finset.sum_Ioc_consecutive (fun m => c m - d) hLM hMU
  have e1 : (∑ m ∈ Finset.Ioc L M, (c m - d)) =
      (∑ m ∈ Finset.Ioc L M, c m) - ((M - L : ℕ) : ℝ) * d := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have e2 : (∑ m ∈ Finset.Ioc M U, (c m - d)) =
      (∑ m ∈ Finset.Ioc M U, c m) - ((U - M : ℕ) : ℝ) * d := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have hk : (U - M = M - L) ∨ (U - M = (M - L) + 1) := by omega
  have hd := le_abs_self d
  have hd' := neg_abs_le d
  rw [abs_le] at h1 h2 ⊢
  rw [e1] at h1
  rw [← hsplit, e1, e2] at h2
  rcases hk with hk | hk
  · rw [hk] at h2
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, abs_nonneg d]
  · rw [hk] at h2
    push_cast at h2
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, abs_nonneg d]

/-- Every value of a Dirichlet character modulo one is one. -/
theorem one_char_apply (χ : DirichletCharacter ℂ 1) (m : ℕ) : χ (m : ZMod 1) = 1 := by
  have h : (m : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [h, map_one]

/-- Page 3, display 1.8 with q equal to one, read as a real sum. -/
theorem real_prefix_of_conditions {x v : ℝ} {b : ℕ → ℝ} (S : Finset ℕ) (Y : ℝ)
    (χ : DirichletCharacter ℂ 1) :
    ‖∑ m ∈ S, ((b m : ℂ) * χ (m : ZMod 1) - Thm2.delta χ * v / Real.log Y)‖ =
      |∑ m ∈ S, (b m - v / Real.log Y)| := by
  have hχ : χ = 1 := Subsingleton.elim _ _
  have hδ : Thm2.delta χ = 1 := by simp [Thm2.delta, hχ]
  have h : (∑ m ∈ S, ((b m : ℂ) * χ (m : ZMod 1) - Thm2.delta χ * v / Real.log Y)) =
      ((∑ m ∈ S, (b m - v / Real.log Y) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [one_char_apply, hδ]
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- Page 3, display 1.8. A short weight satisfying condition iii carries the same mass on the two
halves of J, up to `Y L ^ (-A)` for every A and one bounded term from the integer midpoint.
PROVED. Plain math: `|Σ_{mid < m ≤ U} b(m) - Σ_{L < m ≤ mid} b(m)| ≤ 3 C Y L^(-A) + |v| / log Y`. -/
theorem right_conditions_half_balance {ε B v : ℝ} {b : ℝ → ℕ → ℝ}
    (h : RightConditions ε B v b) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → Real.exp 1 ≤ x →
      |(∑ m ∈ Finset.Ioc (midEnd ε x) (highEnd ε x), b x m) -
          ∑ m ∈ Finset.Ioc (lowEnd ε x) (midEnd ε x), b x m| ≤
        3 * (C * shortY ε x * Real.log x ^ (-A)) + |v / Real.log (shortY ε x)| := by
  obtain ⟨C, hC⟩ := h.2.1 A hA
  refine ⟨C, fun x hxC hxe => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hlog : (1 : ℝ) ≤ Real.log x ^ A := Real.one_le_rpow hlog1 hA.le
  have hY0 : 0 < shortY ε x := Real.rpow_pos_of_pos hx0 _
  have hLU : lowEnd ε x ≤ highEnd ε x :=
    Nat.floor_le_floor (by linarith)
  have hmidU : midEnd ε x ≤ highEnd ε x := by unfold midEnd; omega
  have hLmid : lowEnd ε x ≤ midEnd ε x := by unfold midEnd; omega
  have hUreal : (highEnd ε x : ℝ) ≤ 2 * shortY ε x := Nat.floor_le (by linarith)
  have key : ∀ t : ℕ, lowEnd ε x ≤ t → t ≤ highEnd ε x →
      |∑ m ∈ Finset.Ioc (lowEnd ε x) t, (b x m - v / Real.log (shortY ε x))| ≤
        C * shortY ε x * Real.log x ^ (-A) := by
    intro t ht1 ht2
    have hf : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ (t : ℝ)) =
        Finset.Ioc (lowEnd ε x) t := by
      ext m
      simp only [rightInterval, lowEnd, highEnd, shortY, Finset.mem_filter, Finset.mem_Ioc,
        Nat.cast_le]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans ht2⟩, h3⟩
    have ht : (t : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      (Nat.cast_le.mpr ht2).trans hUreal
    have hh := hC x hxC 1 le_rfl (by simpa using hlog) 1 (t : ℝ) ht
    rw [hf] at hh
    rw [← real_prefix_of_conditions (x := x) (b := b x) _ _ 1]
    exact hh
  exact half_balance_finite (b x) (v / Real.log (shortY ε x)) _ hLU
    (key _ hLmid hmidU) (key _ hLU le_rfl)

/-- Reindexing a natural interval sum. -/
theorem sum_Ioc_add (f : ℕ → ℝ) (a k : ℕ) :
    ∑ m ∈ Finset.Ioc a (a + k), f m = ∑ i ∈ Finset.range k, f (a + 1 + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]
    congr 2
    omega

/-- Page 51 normalization audit. On J the reciprocal log coefficient puts at least
`Y / (144 ℓ ^ 2)` more mass on the lower half, up to one term at the right end.
PROVED. Plain math: `Σ_{L<m≤mid} 1/log m - Σ_{mid<m≤U} 1/log m ≥ Y/(144 ℓ²) - 1/ℓ`. -/
theorem reciprocal_half_gap {Y : ℝ} (hY : 4 ≤ Y) :
    let L := ⌊Y⌋₊
    let U := ⌊2 * Y⌋₊
    let M := L + (U - L) / 2
    Y / (144 * Real.log Y ^ 2) - 1 / Real.log Y ≤
      (∑ m ∈ Finset.Ioc L M, 1 / Real.log (m : ℝ)) -
        ∑ m ∈ Finset.Ioc M U, 1 / Real.log (m : ℝ) := by
  intro L U M
  have hY0 : 0 < Y := by linarith
  have hℓ : 0 < Real.log Y := Real.log_pos (by linarith)
  set ℓ := Real.log Y with hℓdef
  have hLle : (L : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hLlt : Y < (L : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hUle : (U : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have hUlt : 2 * Y < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLU : L ≤ U := Nat.floor_le_floor (by linarith)
  obtain ⟨k, hk⟩ : ∃ k, M = L + k := ⟨(U - L) / 2, rfl⟩
  have hkU : (U - L) / 2 = k := by omega
  obtain ⟨e, he, hUe⟩ : ∃ e, e ≤ 1 ∧ U = L + k + k + e := ⟨U - (L + k + k), by omega, by omega⟩
  have hkreal : Y / 4 ≤ (k : ℝ) := by
    have : (U : ℝ) = L + k + k + e := by exact_mod_cast hUe
    have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
    nlinarith
  have h2ℓ : Real.log (2 * Y) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num) hY0.ne']
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ Y)
    linarith
  have hterm : ∀ i ∈ Finset.range k,
      1 / (36 * ℓ ^ 2) ≤ 1 / Real.log ((L + 1 + i : ℕ) : ℝ) -
        1 / Real.log ((L + k + 1 + i : ℕ) : ℝ) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    set a : ℝ := ((L + 1 + i : ℕ) : ℝ) with ha
    set c : ℝ := ((L + k + 1 + i : ℕ) : ℝ) with hc
    have hcsum : c = a + k := by simp only [ha, hc]; push_cast; ring
    have hle : L + k + 1 + i ≤ U := by omega
    have hcU : c ≤ 2 * Y := (Nat.cast_le.mpr hle).trans hUle
    have haY : Y ≤ a := by
      simp only [ha]; push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have ha0 : 0 < a := by linarith
    have hc0 : 0 < c := by rw [hcsum]; positivity
    have h98 : (9 / 8) * a ≤ c := by nlinarith
    have hgap : 1 / 9 ≤ Real.log c - Real.log a := by
      have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
      have h2 := Real.log_le_log (by positivity) h98
      rw [Real.log_mul (by norm_num) ha0.ne'] at h2
      norm_num at h1
      linarith
    have hla : ℓ ≤ Real.log a := Real.log_le_log hY0 haY
    have hla0 : 0 < Real.log a := by linarith
    have hlc : Real.log c ≤ 2 * ℓ := (Real.log_le_log hc0 hcU).trans h2ℓ
    have hlc0 : 0 < Real.log c := by linarith
    have hlac : Real.log a ≤ 2 * ℓ := by linarith
    rw [show 1 / Real.log a - 1 / Real.log c =
      (Real.log c - Real.log a) / (Real.log a * Real.log c) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hprod : Real.log a * Real.log c ≤ 4 * ℓ ^ 2 := by nlinarith
    nlinarith
  have hlow : (∑ m ∈ Finset.Ioc L M, 1 / Real.log (m : ℝ)) =
      ∑ i ∈ Finset.range k, 1 / Real.log ((L + 1 + i : ℕ) : ℝ) := by
    rw [hk, sum_Ioc_add (fun m => 1 / Real.log (m : ℝ))]
  have hmid : (∑ m ∈ Finset.Ioc (L + k) (L + k + k), 1 / Real.log (m : ℝ)) =
      ∑ i ∈ Finset.range k, 1 / Real.log ((L + k + 1 + i : ℕ) : ℝ) := by
    rw [sum_Ioc_add (fun m => 1 / Real.log (m : ℝ))]
  have hup : (∑ m ∈ Finset.Ioc M U, 1 / Real.log (m : ℝ)) ≤
      (∑ m ∈ Finset.Ioc (L + k) (L + k + k), 1 / Real.log (m : ℝ)) + 1 / ℓ := by
    rw [hk, hUe]
    have hone : (0 : ℝ) ≤ 1 / ℓ := by positivity
    interval_cases e
    · simpa using hone
    · rw [show L + k + k + 1 = (L + k + k) + 1 by ring,
        Finset.sum_Ioc_succ_top (by omega)]
      have hlast : Y ≤ ((L + k + k + 1 : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have : 1 / Real.log ((L + k + k + 1 : ℕ) : ℝ) ≤ 1 / ℓ :=
        one_div_le_one_div_of_le hℓ (Real.log_le_log hY0 hlast)
      linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_sub_distrib] at hsum
  rw [hlow]
  rw [hmid] at hup
  have hk36 : Y / (144 * ℓ ^ 2) ≤ (k : ℝ) * (1 / (36 * ℓ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have : (k : ℝ) * (1 / (36 * ℓ ^ 2)) * (144 * ℓ ^ 2) = 4 * k := by field_simp; ring
    rw [this]
    linarith
  linarith

/-- Page 3 display 1.8, page 51 and page 52. No constant center serves a coefficient whose
partial sums follow the density 1 / log m to within `K Y / (log Y) ^ 3`. By the prime number
theorem this covers the prime indicator, so the page 51 density is not a true constant density.
This is a statement about a raw candidate. It does not refute the existential leaves of
DecompC165d, whose weight may carry a slowly varying factor.
PROVED. Plain math: `(1.8)` at `A = 3` with any `v` contradicts
`Σ_{L<m≤n} (b(m) - 1/log m) ≪ Y (log Y)^(-3)`. -/
theorem not_right_conditions_of_reciprocal_tracking {ε B v K X : ℝ} {b : ℝ → ℕ → ℝ}
    (hε : 0 ≤ ε) (h : RightConditions ε B v b)
    (htrack : ∀ x : ℝ, X ≤ x → ∀ n : ℕ, n = midEnd ε x ∨ n = highEnd ε x →
      |∑ m ∈ Finset.Ioc (lowEnd ε x) n, (b x m - 1 / Real.log (m : ℝ))| ≤
        K * shortY ε x / Real.log (shortY ε x) ^ 3) : False := by
  obtain ⟨C, hC⟩ := right_conditions_half_balance h (A := 3) (by norm_num)
  set s : ℝ := 11 / 20 + ε with hs
  have hs0 : 11 / 20 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  let D1 : ℝ := 3 * |K| + 3 * |C| * s ^ 3
  let D2 : ℝ := 1 + |v|
  let W : ℝ := 288 * D2 + 144 * D1 + 5
  have hW : 0 < W := by dsimp only [W, D1, D2]; positivity
  let T : ℝ := max (max X C) 1 + W / s + 1
  have hT1 : 1 ≤ T := by
    have h1 := le_max_right (max X C) 1
    have : 0 ≤ W / s := by positivity
    dsimp only [T]; linarith
  let x : ℝ := Real.exp T
  have hxT : T ≤ x := by have := Real.add_one_le_exp T; dsimp only [x]; linarith
  have hmaxT : max (max X C) 1 ≤ T := by
    have : 0 ≤ W / s := by positivity
    dsimp only [T]; linarith
  have hxX : X ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans (hmaxT.trans hxT))
  have hxC : C ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans (hmaxT.trans hxT))
  have hxe : Real.exp 1 ≤ x := Real.exp_le_exp.mpr hT1
  have hlogx : Real.log x = T := Real.log_exp T
  let ℓ : ℝ := s * T
  have hYexp : shortY ε x = Real.exp ℓ := by
    dsimp only [shortY, x, ℓ]
    rw [← Real.exp_mul, mul_comm]
  have hℓW : W ≤ ℓ := by
    have hh : W / s ≤ T := by
      have h1 : 1 ≤ max (max X C) 1 := le_max_right _ _
      dsimp only [T]; linarith
    calc W = s * (W / s) := by field_simp
      _ ≤ s * T := mul_le_mul_of_nonneg_left hh hspos.le
  have hℓ5 : 5 ≤ ℓ := by
    have : 0 ≤ 288 * D2 + 144 * D1 := by dsimp only [D1, D2]; positivity
    dsimp only [W] at hℓW; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hlogY : Real.log (shortY ε x) = ℓ := by rw [hYexp, Real.log_exp]
  have hYquad : ℓ ^ 2 / 2 ≤ shortY ε x := by
    rw [hYexp]
    have := Real.quadratic_le_exp_of_nonneg hℓ0.le
    nlinarith
  have hY4 : 4 ≤ shortY ε x := by nlinarith
  have hbal := hC x hxC hxe
  rw [hlogY, Real.rpow_neg (by rw [hlogx]; linarith), hlogx] at hbal
  have hgap := reciprocal_half_gap hY4
  simp only at hgap
  rw [hlogY] at hgap
  have ht1 := htrack x hxX _ (Or.inl rfl)
  have ht2 := htrack x hxX _ (Or.inr rfl)
  rw [hlogY] at ht1 ht2
  have hLmid : lowEnd ε x ≤ midEnd ε x := by unfold midEnd; omega
  have hLU : lowEnd ε x ≤ highEnd ε x := Nat.floor_le_floor (by linarith)
  have hmidU : midEnd ε x ≤ highEnd ε x := by unfold midEnd; omega
  rw [← Finset.sum_Ioc_consecutive _ hLmid hmidU, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib] at ht2
  rw [Finset.sum_sub_distrib] at ht1
  set Sl := ∑ m ∈ Finset.Ioc (lowEnd ε x) (midEnd ε x), b x m
  set Su := ∑ m ∈ Finset.Ioc (midEnd ε x) (highEnd ε x), b x m
  set Fl := ∑ m ∈ Finset.Ioc (lowEnd ε x) (midEnd ε x), 1 / Real.log (m : ℝ)
  set Fu := ∑ m ∈ Finset.Ioc (midEnd ε x) (highEnd ε x), 1 / Real.log (m : ℝ)
  set Y := shortY ε x
  have hY0 : 0 < Y := by linarith
  have hgapF : Y / (144 * ℓ ^ 2) - 1 / ℓ ≤ Fl - Fu := hgap
  rw [abs_le] at ht1 ht2 hbal
  have hTpow : T ^ (3 : ℝ) = T ^ 3 := by norm_cast
  have hTs : (T ^ 3)⁻¹ = s ^ 3 / ℓ ^ 3 := by
    have : T ≠ 0 := by linarith
    dsimp only [ℓ]; field_simp
  rw [hTpow, hTs] at hbal
  have hK : K * Y / ℓ ^ 3 ≤ |K| * Y / ℓ ^ 3 := by
    have : K * Y ≤ |K| * Y := mul_le_mul_of_nonneg_right (le_abs_self K) hY0.le
    exact div_le_div_of_nonneg_right this (by positivity)
  have hCt : C * Y * (s ^ 3 / ℓ ^ 3) ≤ |C| * s ^ 3 * Y / ℓ ^ 3 := by
    have h1 : C * Y * (s ^ 3 / ℓ ^ 3) = C * (s ^ 3 * Y / ℓ ^ 3) := by ring
    have h2 : |C| * s ^ 3 * Y / ℓ ^ 3 = |C| * (s ^ 3 * Y / ℓ ^ 3) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hv : |v / ℓ| = |v| / ℓ := by rw [abs_div, abs_of_pos hℓ0]
  rw [hv] at hbal
  have hmain : Y / (144 * ℓ ^ 2) ≤ D2 / ℓ + D1 * Y / ℓ ^ 3 := by
    have e1 : D2 / ℓ = 1 / ℓ + |v| / ℓ := by dsimp only [D2]; ring
    have e2 : D1 * Y / ℓ ^ 3 = 3 * (|K| * Y / ℓ ^ 3) + 3 * (|C| * s ^ 3 * Y / ℓ ^ 3) := by
      dsimp only [D1]; ring
    rw [e1, e2]
    linarith [ht1.1, ht1.2, ht2.1, ht2.2, hbal.1, hbal.2]
  have hclear : ℓ ≤ 144 * D2 * (ℓ ^ 2 / Y) + 144 * D1 := by
    have h1 := mul_le_mul_of_nonneg_right hmain
      (show 0 ≤ 144 * ℓ ^ 3 / Y by positivity)
    have e3 : Y / (144 * ℓ ^ 2) * (144 * ℓ ^ 3 / Y) = ℓ := by field_simp
    have e4 : (D2 / ℓ + D1 * Y / ℓ ^ 3) * (144 * ℓ ^ 3 / Y) =
        144 * D2 * (ℓ ^ 2 / Y) + 144 * D1 := by field_simp
    rwa [e3, e4] at h1
  have hratio : ℓ ^ 2 / Y ≤ 2 := by
    rw [div_le_iff₀ hY0]; linarith
  have hD2 : 0 ≤ D2 := by dsimp only [D2]; positivity
  have : 144 * D2 * (ℓ ^ 2 / Y) ≤ 144 * D2 * 2 :=
    mul_le_mul_of_nonneg_left hratio (by positivity)
  dsimp only [W] at hℓW
  linarith

/-- The model coefficient on page 51: no constant center serves `1 / log m` itself. This is the
vacuity instance of the tracking hypothesis above, with K equal to zero. PROVED.
Plain math: `b(m) = 1/log m` fails `(1.8)` for every constant `v`. -/
theorem reciprocal_model_not_right_conditions {ε B v : ℝ} (hε : 0 ≤ ε) :
    ¬ RightConditions ε B v (fun _ m => 1 / Real.log (m : ℝ)) := by
  intro h
  refine not_right_conditions_of_reciprocal_tracking (K := 0) (X := 0) hε h ?_
  intro x _ n _
  simp

/-- Pages 3 and 52. A factor that turns a general variable center w into a constant center u.
CONDITIONAL on the raw centered partial sums. `Task387.logarithmic_center_rescaling` is the case
`w = v / log m`, which is not the density of the raw page 51 or page 53 coefficient. -/
theorem density_center_rescaling_mono (f : ℕ → ℝ) (c w : ℕ → ℂ) (d u : ℂ) (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hf : Monotone f) (hb : ∀ i < n, 1 ≤ f i ∧ f i ≤ 2)
    (hfw : ∀ i < n, (f i : ℂ) * w i = u)
    (hc : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, (c i - d * w i)‖ ≤ R) :
    ‖∑ i ∈ Finset.range n, ((f i : ℂ) * c i - d * u)‖ ≤ 3 * R := by
  have h := Task387.monotone_rescaling_partial_sum_bound f (fun i => c i - d * w i) n hR hf hb hc
  convert h using 2
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hfw i (Finset.mem_range.mp hi), Complex.real_smul]
  ring

/-- The decreasing version of `density_center_rescaling_mono`, at the cost of 6 in place of 3.
CONDITIONAL on the raw centered partial sums. -/
theorem density_center_rescaling_anti (f : ℕ → ℝ) (c w : ℕ → ℂ) (d u : ℂ) (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hf : Antitone f) (hb : ∀ i < n, 1 ≤ f i ∧ f i ≤ 2)
    (hfw : ∀ i < n, (f i : ℂ) * w i = u)
    (hc : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, (c i - d * w i)‖ ≤ R) :
    ‖∑ i ∈ Finset.range n, ((f i : ℂ) * c i - d * u)‖ ≤ 6 * R := by
  have h := Task387.monotone_rescaling_partial_sum_bound (fun i => 3 - f i)
    (fun i => c i - d * w i) n hR (fun i j hij => by show 3 - f i ≤ 3 - f j; linarith [hf hij])
    (fun i hi => ⟨by linarith [(hb i hi).2], by linarith [(hb i hi).1]⟩) hc
  have h0 := hc n le_rfl
  have hid : (∑ i ∈ Finset.range n, ((f i : ℂ) * c i - d * u)) =
      3 * (∑ i ∈ Finset.range n, (c i - d * w i)) -
        ∑ i ∈ Finset.range n, (3 - f i) • (c i - d * w i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hfw i (Finset.mem_range.mp hi), Complex.real_smul]
    push_cast
    ring
  rw [hid]
  calc _ ≤ ‖3 * ∑ i ∈ Finset.range n, (c i - d * w i)‖ + _ := norm_sub_le _ _
    _ ≤ 3 * R + 3 * R := by
      gcongr
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ 3)
    _ = 6 * R := by ring

open MeanSquareC165

/-- Page 11, display 3.3. Leaf 2 of SPLIT_hybrid_mean_square is the sealed target with one more
hypothesis. CONDITIONAL on its own target, so that SPLIT reduces nothing. -/
theorem split_qt_of_target (h : Lemma1MeanSquare) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        F ≤ (q : ℝ) * T → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C, hC, hb⟩ := h B c1 c2 hc1 hc2
  exact ⟨C, hC, fun x F T q S a ha hx hF hFx hT hTx hq hqx _ hs ht =>
    hb x F T q S a ha hx hF hFx hT hTx hq hqx hs ht⟩

/-- Page 11, display 3.3. Leaf 3 of SPLIT_hybrid_mean_square, same remark. -/
theorem split_F_of_target (h : Lemma1MeanSquare) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        (q : ℝ) * T ≤ F → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C, hC, hb⟩ := h B c1 c2 hc1 hc2
  exact ⟨C, hC, fun x F T q S a ha hx hF hFx hT hTx hq hqx _ hs ht =>
    hb x F T q S a ha hx hF hFx hT hTx hq hqx hs ht⟩

/-- Page 11, display 3.4. The second branch of SPLIT_hybrid_large_values follows from its target
with constant 2 C, so that SPLIT reduces nothing. CONDITIONAL on its own target. -/
theorem split_second_branch_of_target (h : Lemma1LargeValues) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T V : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
        Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
        energy a c1 c2 F ^ 2 * ((q : ℝ) * T) ≤ V ^ 4 →
        (S.card : ℝ) ≤ C * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2) := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C, hC, hb⟩ := h B c1 c2 hc1 hc2
  refine ⟨2 * C, by positivity, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hs ht hp hreg
  have hE : 0 ≤ energy a c1 c2 F := by
    apply Finset.sum_nonneg; intro n _; positivity
  have hF0 : 0 ≤ F := by linarith
  have hkey : energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6 ≤
      energy a c1 c2 F * F / V ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hreg
      (show 0 ≤ energy a c1 c2 F * F * V ^ 2 by positivity)
    nlinarith
  have hb' := hb x F T V q S a ha hx hF hFx hT hTx hq hqx hV hs ht hp
  have hC' : 0 ≤ C * Real.log x ^ 2 := by positivity
  calc (S.card : ℝ) ≤ _ := hb'
    _ ≤ C * Real.log x ^ 2 * (energy a c1 c2 F * F / V ^ 2 + energy a c1 c2 F * F / V ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC'
    _ = _ := by ring

/-- Page 11, display 3.4. The third branch of SPLIT_hybrid_large_values, same remark. -/
theorem split_third_branch_of_target (h : Lemma1LargeValues) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T V : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
        Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
        V ^ 4 ≤ energy a c1 c2 F ^ 2 * ((q : ℝ) * T) →
        (S.card : ℝ) ≤
          C * Real.log x ^ 2 * (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C, hC, hb⟩ := h B c1 c2 hc1 hc2
  refine ⟨2 * C, by positivity, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hs ht hp hreg
  have hE : 0 ≤ energy a c1 c2 F := by
    apply Finset.sum_nonneg; intro n _; positivity
  have hF0 : 0 ≤ F := by linarith
  have hkey : energy a c1 c2 F * F / V ^ 2 ≤
      energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hreg
      (show 0 ≤ energy a c1 c2 F * F * V ^ 2 by positivity)
    nlinarith
  have hb' := hb x F T V q S a ha hx hF hFx hT hTx hq hqx hV hs ht hp
  have hC' : 0 ≤ C * Real.log x ^ 2 := by positivity
  calc (S.card : ℝ) ≤ _ := hb'
    _ ≤ C * Real.log x ^ 2 * (energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6 +
          energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6) :=
        mul_le_mul_of_nonneg_left (by linarith) hC'
    _ = _ := by ring

#print axioms half_balance_finite
#print axioms right_conditions_half_balance
#print axioms reciprocal_half_gap
#print axioms not_right_conditions_of_reciprocal_tracking
#print axioms reciprocal_model_not_right_conditions
#print axioms density_center_rescaling_mono
#print axioms density_center_rescaling_anti
#print axioms split_qt_of_target
#print axioms split_F_of_target
#print axioms split_second_branch_of_target
#print axioms split_third_branch_of_target

end LeanLab.BHP1997.Audit1624
