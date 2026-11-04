/-
P0069, pages 1 and 24 to 26. Unit U-1617. Refutation of the old form of equation 4.2.
Old `Holds42` compared the sum over I, of width 2Y, with Y/y1 times the sum over I1.
`lemma11Old_false` proves the old `Lemma11` false: a trapezoid coefficient family equal to 1 on
[5x/8, x] meets the coefficient bound and the mean value hypothesis 4.1 at both signs of t, and
then the old `Holds42` fails. The old statements survive here verbatim.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.DecompBounds
open Finset
namespace LeanLab.BakerHarmanPintz1997.Audit1617
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-! ### The old statements, verbatim -/

/-- Old `Holds42`, verbatim, sum over I of width 2Y against factor Y/y1. FALSE for positive
density, see `not_holds42Old_of_plateau`. -/
def Holds42Old (ε : ℝ) (c : ℝ → ℕ → ℂ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A →
    ∀ χ : DirichletCharacter ℂ q,
      ‖∑ k ∈ Iset ε x, c x k * χ (k : ZMod q) -
        ((Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)‖ ≤
      C * Yof ε x / L x ^ A

/-- Old `Lemma11`, verbatim. -/
def Lemma11Old : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (B : ℝ) (c : ℝ → ℕ → ℂ),
    (∀ x k, ‖c x k‖ ≤ tau k ^ B) →
    (∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A →
      ∀ χ : DirichletCharacter ℂ q,
        ∫ t in (T0 x)..(T1 ε x),
          ‖(⟨c x, Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t)‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) →
    Holds42Old ε c

/-! ### A trapezoid as a combination of ramps -/

/-- The ramp. -/
noncomputable def rho (u : ℝ) : ℝ := max u 0

theorem rho_ite (u : ℝ) : rho u = if 0 ≤ u then u else 0 := by
  unfold rho
  split_ifs with h
  · exact max_eq_left h
  · exact max_eq_right (le_of_lt (not_le.mp h))

/-- The trapezoid: 0 up to a, rising to 1 at a + D, 1 up to b, falling to 0 at b + D. -/
noncomputable def tz (a D b : ℕ) (u : ℝ) : ℝ :=
  (rho (u - a) - rho (u - ((a : ℝ) + D)) - rho (u - b) + rho (u - ((b : ℝ) + D))) / D

theorem tz_bounds {a D b : ℕ} (hD : 0 < D) (hab : a + D ≤ b) (u : ℝ) :
    0 ≤ tz a D b u ∧ tz a D b u ≤ 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hab' : (a : ℝ) + D ≤ b := by exact_mod_cast hab
  unfold tz
  simp only [rho_ite]
  constructor
  · apply div_nonneg _ hD'.le
    split_ifs <;> linarith
  · rw [div_le_one hD']
    split_ifs <;> linarith

theorem tz_left {a D b : ℕ} (hD : 0 < D) (hab : a + D ≤ b) {u : ℝ} (hu : u ≤ a) :
    tz a D b u = 0 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hab' : (a : ℝ) + D ≤ b := by exact_mod_cast hab
  unfold tz
  simp only [rho_ite]
  rw [div_eq_zero_iff]
  left
  split_ifs <;> linarith

theorem tz_right {a D b : ℕ} (hD : 0 < D) (hab : a + D ≤ b) {u : ℝ} (hu : (b : ℝ) + D ≤ u) :
    tz a D b u = 0 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hab' : (a : ℝ) + D ≤ b := by exact_mod_cast hab
  unfold tz
  simp only [rho_ite]
  rw [div_eq_zero_iff]
  left
  split_ifs <;> linarith

theorem tz_one {a D b : ℕ} (hD : 0 < D) (hab : a + D ≤ b) {u : ℝ} (h1 : (a : ℝ) + D ≤ u)
    (h2 : u ≤ b) : tz a D b u = 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hab' : (a : ℝ) + D ≤ b := by exact_mod_cast hab
  unfold tz
  simp only [rho_ite]
  rw [div_eq_one_iff_eq hD'.ne']
  split_ifs <;> linarith

/-- The second difference of a ramp at step q. -/
noncomputable def R2 (q a j : ℝ) : ℝ := rho (j + q - a) + rho (j - q - a) - 2 * rho (j - a)

theorem R2_abs {q : ℝ} (hq : 0 ≤ q) (a j : ℝ) : |R2 q a j| ≤ q := by
  unfold R2
  simp only [rho_ite]
  rw [abs_le]
  constructor <;> split_ifs <;> linarith

theorem R2_zero {q a j : ℝ} (hq : 0 ≤ q) (h : q ≤ j - a ∨ j - a ≤ -q) : R2 q a j = 0 := by
  unfold R2
  simp only [rho_ite]
  rcases h with h | h <;> split_ifs <;> linarith

theorem tz_secdiff (a D b : ℕ) (q j : ℝ) :
    tz a D b (j + q) + tz a D b (j - q) - 2 * tz a D b j =
      (R2 q a j - R2 q ((a : ℝ) + D) j - R2 q b j + R2 q ((b : ℝ) + D) j) / D := by
  unfold tz R2
  ring

theorem sum_R2 (q M : ℕ) (a : ℕ) :
    ∑ j ∈ range M, |R2 q a j| ≤ 2 * (q : ℝ) ^ 2 := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : ∀ j ∈ range M, |R2 q a j| ≤ if a < j + q ∧ j < a + q then (q : ℝ) else 0 := by
    intro j _
    split_ifs with h
    · exact R2_abs hq _ _
    · rw [R2_zero hq, abs_zero]
      by_cases h' : a < j + q
      · have : a + q ≤ j := by omega
        left
        have : (a : ℝ) + q ≤ j := by exact_mod_cast this
        linarith
      · have : j + q ≤ a := by omega
        right
        have : (j : ℝ) + q ≤ a := by exact_mod_cast this
        linarith
  refine (sum_le_sum h1).trans ?_
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
  have hsub : (range M).filter (fun j => a < j + q ∧ j < a + q) ⊆ Ico (a - q) (a + q) := by
    intro j hj
    have := (mem_filter.mp hj).2
    exact mem_Ico.mpr ⟨by omega, this.2⟩
  have hc : ((range M).filter (fun j => a < j + q ∧ j < a + q)).card ≤ 2 * q := by
    refine (card_le_card hsub).trans ?_
    rw [Nat.card_Ico]
    omega
  have hc' : (((range M).filter (fun j => a < j + q ∧ j < a + q)).card : ℝ) ≤ 2 * q := by
    exact_mod_cast hc
  nlinarith

/-- Reindexing a sum by the shift q, with vanishing at both ends. -/
theorem shift_sum (A B : ℕ → ℂ) {q M : ℕ} (hq : q ≤ M) (h1 : ∀ k, k < q → A k * B (k - q) = 0)
    (h2 : ∀ j, j < M → M ≤ j + q → A (j + q) * B j = 0) :
    ∑ k ∈ range M, A k * B (k - q) = ∑ j ∈ range M, A (j + q) * B j := by
  obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [Finset.sum_range_add, sum_eq_zero (fun k hk => h1 k (mem_range.mp hk)), zero_add]
  rw [Nat.add_comm q M', Finset.sum_range_add]
  have h0 : ∑ x ∈ range q, A (M' + x + q) * B (M' + x) = 0 :=
    sum_eq_zero fun i hi => h2 _ (by have := mem_range.mp hi; omega) (by omega)
  rw [h0, add_zero]
  apply sum_congr rfl
  intro i _
  rw [show q + i - q = i by omega, Nat.add_comm q i]

/-- The core identity. Summing by parts twice at step q moves the second difference onto the
trapezoid, whose second difference lives near its four corners; periodicity of the character
lets it pass through. No residue classes are needed. -/
theorem core {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a D b M : ℕ} (hD : 0 < D)
    (hab : a + D ≤ b) (hqa : 2 * q ≤ a) (hM : b + D + q ≤ M) (G e : ℕ → ℂ) {Gmax Rmax : ℝ}
    (hGmax : 0 ≤ Gmax) (hRmax : 0 ≤ Rmax)
    (hG : ∀ j, 0 < j → j < M → ‖G j‖ ≤ Gmax)
    (hR : ∀ k, a < k → k < b + D →
      ‖G (k + q) + G (k - q) - 2 * G k - (q : ℂ) ^ 2 * e k‖ ≤ Rmax) :
    (q : ℝ) ^ 2 * ‖∑ k ∈ range M, ((tz a D b k : ℝ) : ℂ) * χ (k : ZMod q) * e k‖ ≤
      8 * (q : ℝ) ^ 2 / D * Gmax + M * Rmax := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set v : ℕ → ℂ := fun k => ((tz a D b k : ℝ) : ℂ) * χ (k : ZMod q) with hvdef
  have hvl : ∀ k, k ≤ a → v k = 0 := by
    intro k hk
    have : (k : ℝ) ≤ a := by exact_mod_cast hk
    simp [hvdef, tz_left hD hab this]
  have hvr : ∀ k, b + D ≤ k → v k = 0 := by
    intro k hk
    have : (b : ℝ) + D ≤ k := by exact_mod_cast hk
    simp [hvdef, tz_right hD hab this]
  have hvn : ∀ k, ‖v k‖ ≤ 1 := by
    intro k
    simp only [hvdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := tz_bounds hD hab (k : ℝ)
    rw [abs_of_nonneg hb.1]
    exact mul_le_one₀ hb.2 (norm_nonneg _) (χ.norm_le_one _)
  set Rk : ℕ → ℂ := fun k => G (k + q) + G (k - q) - 2 * G k - (q : ℂ) ^ 2 * e k with hRk
  have s1 : ∑ k ∈ range M, G k * v (k - q) = ∑ j ∈ range M, G (j + q) * v j :=
    shift_sum G v (by omega)
      (fun k hk => by rw [hvl (k - q) (by omega), mul_zero])
      (fun j _ hj => by rw [hvr j (by omega), mul_zero])
  have s2 : ∑ k ∈ range M, v k * G (k - q) = ∑ j ∈ range M, v (j + q) * G j :=
    shift_sum v G (by omega)
      (fun k hk => by rw [hvl k (by omega), zero_mul])
      (fun j _ hj => by rw [hvr (j + q) (by omega), zero_mul])
  have key : (q : ℂ) ^ 2 * ∑ k ∈ range M, v k * e k =
      (∑ j ∈ range M, G j * (v (j - q) + v (j + q) - 2 * v j)) -
        ∑ k ∈ range M, v k * Rk k := by
    have e1 : ∑ j ∈ range M, G j * (v (j - q) + v (j + q) - 2 * v j) =
        ∑ k ∈ range M, G k * v (k - q) + ∑ k ∈ range M, v k * G (k - q) -
          ∑ k ∈ range M, 2 * (v k * G k) := by
      rw [s2, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro k _
      ring
    rw [e1, s1, mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    simp only [hRk]
    ring
  set Dw : ℕ → ℝ := fun j => tz a D b ((j : ℝ) + q) + tz a D b ((j : ℝ) - q) -
    2 * tz a D b (j : ℝ) with hDw
  have hsumDw : ∑ j ∈ range M, |Dw j| ≤ 8 * (q : ℝ) ^ 2 / D := by
    have hp : ∀ j ∈ range M, |Dw j| ≤
        (|R2 q a j| + |R2 q ((a + D : ℕ) : ℝ) j| + |R2 q b j| +
          |R2 q ((b + D : ℕ) : ℝ) j|) / D := by
      intro j _
      simp only [hDw]
      rw [tz_secdiff, abs_div, abs_of_pos hD']
      apply div_le_div_of_nonneg_right _ hD'.le
      push_cast
      have t1 := abs_sub (R2 q a j - R2 q ((a : ℝ) + D) j - R2 q b j) (R2 q ((b : ℝ) + D) j)
      have t0 := abs_add_le (R2 q a j - R2 q ((a : ℝ) + D) j - R2 q b j) (R2 q ((b : ℝ) + D) j)
      have t2 := abs_sub (R2 q a j - R2 q ((a : ℝ) + D) j) (R2 q b j)
      have t3 := abs_sub (R2 q a j) (R2 q ((a : ℝ) + D) j)
      linarith
    refine (sum_le_sum hp).trans ?_
    rw [← sum_div, sum_add_distrib, sum_add_distrib, sum_add_distrib]
    apply div_le_div_of_nonneg_right _ hD'.le
    have := sum_R2 q M a
    have := sum_R2 q M (a + D)
    have := sum_R2 q M b
    have := sum_R2 q M (b + D)
    linarith
  have hfirst : ‖∑ j ∈ range M, G j * (v (j - q) + v (j + q) - 2 * v j)‖ ≤
      8 * (q : ℝ) ^ 2 / D * Gmax := by
    refine (norm_sum_le _ _).trans ?_
    have hp : ∀ j ∈ range M, ‖G j * (v (j - q) + v (j + q) - 2 * v j)‖ ≤ |Dw j| * Gmax := by
      intro j hj
      by_cases hjq : q ≤ j
      · have hj0 : 0 < j := by omega
        have hc1 : (((j - q : ℕ) : ℕ) : ZMod q) = (j : ZMod q) := by
          rw [Nat.cast_sub hjq]; simp
        have hc2 : (((j + q : ℕ) : ℕ) : ZMod q) = (j : ZMod q) := by simp
        have hexp : v (j - q) + v (j + q) - 2 * v j = ((Dw j : ℝ) : ℂ) * χ (j : ZMod q) := by
          simp only [hvdef, hDw, hc1, hc2]
          rw [Nat.cast_sub hjq]
          push_cast
          ring
        rw [hexp, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 := hG j hj0 (mem_range.mp hj)
        have h2 : ‖χ (j : ZMod q)‖ ≤ 1 := χ.norm_le_one _
        calc ‖G j‖ * (|Dw j| * ‖χ (j : ZMod q)‖) ≤ Gmax * (|Dw j| * 1) := by gcongr
          _ = _ := by ring
      · have h0 : v (j - q) = 0 := hvl _ (by omega)
        have h1 : v (j + q) = 0 := hvl _ (by omega)
        have h2 : v j = 0 := hvl _ (by omega)
        rw [h0, h1, h2]
        simp only [zero_add, mul_zero, sub_self, norm_zero]
        positivity
    refine (sum_le_sum hp).trans ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right hsumDw hGmax
  have hsecond : ‖∑ k ∈ range M, v k * Rk k‖ ≤ M * Rmax := by
    refine (norm_sum_le _ _).trans ?_
    have hp : ∀ k ∈ range M, ‖v k * Rk k‖ ≤ Rmax := by
      intro k _
      by_cases h1 : k ≤ a
      · rw [hvl k h1]; simpa using hRmax
      by_cases h2 : b + D ≤ k
      · rw [hvr k h2]; simpa using hRmax
      rw [norm_mul]
      calc ‖v k‖ * ‖Rk k‖ ≤ 1 * Rmax :=
            mul_le_mul (hvn k) (hR k (by omega) (by omega)) (norm_nonneg _) zero_le_one
        _ = Rmax := one_mul _
    refine (sum_le_sum hp).trans ?_
    simp
  have hnq : ‖((q : ℂ) ^ 2)‖ = (q : ℝ) ^ 2 := by simp
  have heq : (q : ℝ) ^ 2 * ‖∑ k ∈ range M, ((tz a D b k : ℝ) : ℂ) * χ (k : ZMod q) * e k‖ =
      ‖(q : ℂ) ^ 2 * ∑ k ∈ range M, v k * e k‖ := by
    rw [norm_mul, hnq]
  rw [heq, key]
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

/-! ### Second difference against second derivative -/

theorem second_diff (G G1 e : ℝ → ℂ) {u h B : ℝ} (hh : 0 ≤ h)
    (hG : ∀ y, u - h ≤ y → y ≤ u + h → HasDerivAt G (G1 y) y)
    (hG1 : ∀ y, u - h ≤ y → y ≤ u + h → HasDerivAt G1 (e y) y)
    (hB : ∀ y, u - h ≤ y → y ≤ u + h → ‖e y - e u‖ ≤ B) :
    ‖G (u + h) + G (u - h) - 2 * G u - (h : ℂ) ^ 2 * e u‖ ≤ 2 * B * h * h := by
  have hB0 : 0 ≤ B := by
    have := hB u (by linarith) (by linarith)
    simpa using this
  have hv : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := fun v => by
    simpa using (hasDerivAt_id v).ofReal_comp
  let ψ : ℝ → ℂ := fun v => G1 (u + v) - G1 (u - v) - 2 * (v : ℂ) * e u
  let φ : ℝ → ℂ := fun v => G (u + v) + G (u - v) - 2 * G u - (v : ℂ) ^ 2 * e u
  have hψ : ∀ v ∈ Set.Icc 0 h, HasDerivAt ψ (e (u + v) + e (u - v) - 2 * e u) v := by
    intro v hv'
    have a1 := (hG1 (u + v) (by linarith [hv'.1]) (by linarith [hv'.2])).comp_const_add u v
    have a2 := (hG1 (u - v) (by linarith [hv'.2]) (by linarith [hv'.1])).comp_const_sub u v
    have a3 := ((hv v).const_mul (2 : ℂ)).mul_const (e u)
    convert (a1.sub a2).sub a3 using 1
    ring
  have hφ : ∀ v ∈ Set.Icc 0 h, HasDerivAt φ (ψ v) v := by
    intro v hv'
    have a1 := (hG (u + v) (by linarith [hv'.1]) (by linarith [hv'.2])).comp_const_add u v
    have a2 := (hG (u - v) (by linarith [hv'.2]) (by linarith [hv'.1])).comp_const_sub u v
    have a3 := ((hv v).pow 2).mul_const (e u)
    convert ((a1.add a2).sub_const (2 * G u)).sub a3 using 1
    simp only [ψ]
    simp
    ring
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hφ0 : φ 0 = 0 := by simp [φ]; ring
  have hc : Convex ℝ (Set.Icc (0 : ℝ) h) := convex_Icc 0 h
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) h := ⟨le_rfl, hh⟩
  have hψb : ∀ v ∈ Set.Icc 0 h, ‖ψ v‖ ≤ 2 * B * h := by
    intro v hv'
    have := hc.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 2 * B)
      (fun x hx => (hψ x hx).hasDerivWithinAt) (fun x hx => by
        have e1 := hB (u + x) (by linarith [hx.1]) (by linarith [hx.2])
        have e2 := hB (u - x) (by linarith [hx.2]) (by linarith [hx.1])
        have : e (u + x) + e (u - x) - 2 * e u = (e (u + x) - e u) + (e (u - x) - e u) := by ring
        rw [this]
        exact (norm_add_le _ _).trans (by linarith)) h0mem hv'
    rw [hψ0, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hv'.1] at this
    exact this.trans (mul_le_mul_of_nonneg_left hv'.2 (by positivity))
  have := hc.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 2 * B * h)
    (fun x hx => (hφ x hx).hasDerivWithinAt) hψb h0mem ⟨hh, le_rfl⟩
  rw [hφ0, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hh] at this
  exact this


/-! ### The complex powers -/

noncomputable def E0 (s : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (-s)
noncomputable def G1 (s : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (1 - s) / (1 - s)
noncomputable def G2 (s : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (2 - s) / ((2 - s) * (1 - s))

theorem half_re (t : ℝ) : (half t).re = 1 / 2 := by
  norm_num [half]

theorem half_im (t : ℝ) : (half t).im = t := by
  norm_num [half]

theorem hasDeriv_G1 {s : ℂ} (hs : s ≠ 1) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (G1 s) (E0 s y) y := by
  have := hasDerivAt_ofReal_cpow_const' hy (r := -s) (fun h => hs (neg_injective h))
  rw [show -s + 1 = 1 - s by ring] at this
  exact this

theorem hasDeriv_G2 {s : ℂ} (hs2 : s ≠ 2) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (G2 s) (G1 s y) y := by
  have hr : 1 - s ≠ -1 := fun h => hs2 (by linear_combination -h)
  have h1 := hasDerivAt_ofReal_cpow_const' hy (r := 1 - s) hr
  rw [show 1 - s + 1 = 2 - s by ring] at h1
  have h2 := h1.div_const (1 - s)
  convert h2 using 1
  · funext z
    simp only [G2]
    rw [div_div]
  · rfl

theorem hasDeriv_E0 {s : ℂ} (hs : s ≠ 0) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (E0 s) ((-s) * (y : ℂ) ^ (-s - 1)) y :=
  hasDerivAt_ofReal_cpow_const hy (neg_ne_zero.mpr hs)

theorem E0_lip {s : ℂ} (hre : s.re = 1 / 2) (hs : s ≠ 0) {u h w y : ℝ} (hw : 0 < w)
    (hu : w ≤ u - h) (h1 : u - h ≤ y) (h2 : y ≤ u + h) :
    ‖E0 s y - E0 s u‖ ≤ ‖s‖ * w ^ (-(3 / 2) : ℝ) * h := by
  have hh : 0 ≤ h := by linarith
  have := (convex_Icc (u - h) (u + h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := ‖s‖ * w ^ (-(3 / 2) : ℝ)) (f := E0 s)
    (fun z hz => (hasDeriv_E0 hs (by
      have hz1 := hz.1
      have hz0 : 0 < z := by linarith
      exact hz0.ne')).hasDerivWithinAt)
    (fun z hz => by
      have hzw : w ≤ z := hu.trans hz.1
      have hz0 : 0 < z := hw.trans_le hzw
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hz0]
      have hexp : (-s - 1).re = -(3 / 2) := by simp [hre]; norm_num
      rw [hexp]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hw hzw (by norm_num)) (norm_nonneg s))
    (show u ∈ Set.Icc (u - h) (u + h) from ⟨by linarith, by linarith⟩)
    (show y ∈ Set.Icc (u - h) (u + h) from ⟨h1, h2⟩)
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-! ### The trapezoid family -/

noncomputable def aX (x : ℝ) : ℕ := ⌊x / 2⌋₊
noncomputable def dX (x : ℝ) : ℕ := ⌊x / 8⌋₊
noncomputable def bX (x : ℝ) : ℕ := ⌊x⌋₊

/-- The coefficient family: 0 below x/2, 1 on [5x/8, x], 0 above 9x/8, piecewise linear. -/
noncomputable def cP (x : ℝ) (k : ℕ) : ℂ := ((tz (aX x) (dX x) (bX x) k : ℝ) : ℂ)

theorem params {x : ℝ} (hx : 64 ≤ x) :
    0 < dX x ∧ aX x + dX x ≤ bX x ∧ x / 2 - 1 < aX x ∧ (aX x : ℝ) ≤ x / 2 ∧
      x / 16 ≤ dX x ∧ (dX x : ℝ) ≤ x / 8 ∧ (bX x : ℝ) ≤ x ∧ x - 1 < bX x := by
  have a1 : (aX x : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
  have a2 : x / 2 < aX x + 1 := Nat.lt_floor_add_one _
  have d1 : (dX x : ℝ) ≤ x / 8 := Nat.floor_le (by linarith)
  have d2 : x / 8 < dX x + 1 := Nat.lt_floor_add_one _
  have b1 : (bX x : ℝ) ≤ x := Nat.floor_le (by linarith)
  have b2 : x < bX x + 1 := Nat.lt_floor_add_one _
  have hd : x / 16 ≤ dX x := by linarith
  refine ⟨?_, ?_, by linarith, a1, hd, d1, b1, by linarith⟩
  · have : (0 : ℝ) < dX x := by linarith
    exact_mod_cast this
  · apply Nat.le_floor
    push_cast
    linarith

/-- Pointwise bound on the Dirichlet polynomial of the trapezoid, any character. -/
theorem dp_bound {x t : ℝ} {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hx : 64 ≤ x)
    (hq : (q : ℝ) ≤ x / 16) (ht : 1 ≤ |t|) :
    ‖(⟨cP x, Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t)‖ ≤
      384 * x ^ (1 / 2 : ℝ) / t ^ 2 + 64 * q * |t| / x ^ (1 / 2 : ℝ) := by
  obtain ⟨hD, hab, ha1, ha2, hd1, hd2, hb1, hb2⟩ := params hx
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hx0 : 0 < x := by linarith
  have hDR : (0 : ℝ) < dX x := by exact_mod_cast hD
  set s := half t with hsdef
  have hre : s.re = 1 / 2 := half_re t
  have him : s.im = t := half_im t
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have hs2 : s ≠ 2 := fun h => by rw [h] at hre; norm_num at hre
  set a := aX x with hadef
  set D := dX x with hDdef
  set b := bX x with hbdef
  set M := b + D + q with hMdef
  have hMR : (M : ℝ) ≤ 2 * x := by
    simp only [hMdef]; push_cast; linarith
  have hqa : 2 * q ≤ a := by
    have : (2 * q : ℝ) ≤ a := by linarith
    exact_mod_cast this
  have hzl : ∀ k : ℕ, k ≤ a → cP x k = 0 := by
    intro k hk
    have : (k : ℝ) ≤ a := by exact_mod_cast hk
    simp [cP, tz_left hD hab this, ← hadef, ← hDdef, ← hbdef]
  have hzr : ∀ k : ℕ, b + D ≤ k → cP x k = 0 := by
    intro k hk
    have : (b : ℝ) + D ≤ k := by exact_mod_cast hk
    simp [cP, tz_right hD hab this, ← hadef, ← hDdef, ← hbdef]
  have hsup : b + D ≤ ⌊2 * x⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hS : (⟨cP x, Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t) =
      ∑ k ∈ range M, ((tz a D b k : ℝ) : ℂ) * χ (k : ZMod q) * E0 s k := by
    unfold DP.eval
    dsimp only
    have h1 : ∑ n ∈ Ioo a (b + D), cP x n * χ (n : ZMod q) * (n : ℂ) ^ (-half t) =
        ∑ n ∈ Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, cP x n * χ (n : ZMod q) * (n : ℂ) ^ (-half t) := by
      apply sum_subset
      · intro k hk
        have := mem_Ioo.mp hk
        exact mem_Ioc.mpr ⟨this.1, by omega⟩
      · intro k _ hk
        have : k ≤ a ∨ b + D ≤ k := by
          by_contra hc
          exact hk (mem_Ioo.mpr (by omega))
        rcases this with h | h
        · rw [hzl k h]; simp
        · rw [hzr k h]; simp
    have h2 : ∑ n ∈ Ioo a (b + D), cP x n * χ (n : ZMod q) * (n : ℂ) ^ (-half t) =
        ∑ n ∈ range M, cP x n * χ (n : ZMod q) * (n : ℂ) ^ (-half t) := by
      apply sum_subset
      · intro k hk
        have := mem_Ioo.mp hk
        exact mem_range.mpr (by omega)
      · intro k _ hk
        have : k ≤ a ∨ b + D ≤ k := by
          by_contra hc
          exact hk (mem_Ioo.mpr (by omega))
        rcases this with h | h
        · rw [hzl k h]; simp
        · rw [hzr k h]; simp
    rw [← h1, h2]
    apply sum_congr rfl
    intro k _
    simp only [cP, E0, Complex.ofReal_natCast, ← hadef, ← hDdef, ← hbdef, hsdef]
  set w : ℝ := x / 4 with hw
  have hw0 : 0 < w := by positivity
  set Gmax : ℝ := (2 * x) ^ (3 / 2 : ℝ) / t ^ 2 with hGmaxdef
  have ht0 : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hGmax0 : 0 ≤ Gmax := by positivity
  set Bd : ℝ := ‖s‖ * w ^ (-(3 / 2) : ℝ) * q with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hmain := core χ hD hab hqa (le_refl M) (fun j => G2 s (j : ℝ)) (fun k => E0 s (k : ℝ))
    (Gmax := Gmax) (Rmax := 2 * Bd * q * q) hGmax0 (by positivity)
    (fun j hj hjM => by
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
      have hjM' : (j : ℝ) ≤ 2 * x := by
        have : (j : ℝ) ≤ M := by exact_mod_cast hjM.le
        linarith
      simp only [G2]
      rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hj0]
      have hexp : (2 - s).re = 3 / 2 := by simp [hre]; norm_num
      rw [hexp]
      have n1 : |t| ≤ ‖2 - s‖ := by
        have := Complex.abs_im_le_norm (2 - s)
        simpa [him] using this
      have n2 : |t| ≤ ‖1 - s‖ := by
        have := Complex.abs_im_le_norm (1 - s)
        simpa [him] using this
      have n3 : t ^ 2 ≤ ‖2 - s‖ * ‖1 - s‖ := by
        rw [← sq_abs, sq]
        exact mul_le_mul n1 n2 ht0.le (norm_nonneg _)
      exact div_le_div₀ (by positivity)
        (Real.rpow_le_rpow hj0.le hjM' (by norm_num)) ht2 n3)
    (fun k hk1 hk2 => by
      have hk1R : (a : ℝ) + 1 ≤ k := by exact_mod_cast hk1
      have hkq : q ≤ k := by omega
      have hsd := second_diff (G2 s) (G1 s) (E0 s) (u := (k : ℝ)) (h := (q : ℝ)) (B := Bd)
        hqR.le
        (fun y h1 _ => hasDeriv_G2 hs2 (by
          have : 0 < y := by linarith
          exact this.ne'))
        (fun y h1 _ => hasDeriv_G1 hs1 (by
          have : 0 < y := by linarith
          exact this.ne'))
        (fun y h1 h2 => E0_lip hre hs0 hw0 (by simp only [hw]; linarith) h1 h2)
      have c1 : ((k + q : ℕ) : ℝ) = (k : ℝ) + q := by push_cast; ring
      have c2 : ((k - q : ℕ) : ℝ) = (k : ℝ) - q := by rw [Nat.cast_sub hkq]
      rw [c1, c2]
      simpa using hsd)
  rw [hS]
  set F := ∑ k ∈ range M, ((tz a D b k : ℝ) : ℂ) * χ (k : ZMod q) * E0 s (k : ℝ) with hF
  set S : ℝ := x ^ (1 / 2 : ℝ) with hSdef
  have hSpos : 0 < S := by positivity
  have hSS : S * S = x := by
    rw [hSdef, ← Real.rpow_add hx0]; norm_num
  have hrt2 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
    have e1 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
        Real.sqrt_eq_rpow]
    have e2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [e1]; linarith
  have hx32 : x ^ (3 / 2 : ℝ) = x * S := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have h3 : (2 * x) ^ (3 / 2 : ℝ) ≤ 3 * x * S := by
    rw [Real.mul_rpow (by norm_num) hx0.le, hx32]
    have : 0 ≤ x * S := by positivity
    nlinarith
  have h4 : w ^ (-(3 / 2) : ℝ) = 8 / (x * S) := by
    rw [Real.rpow_neg hw0.le, hw, Real.div_rpow hx0.le (by norm_num), hx32]
    have : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [this]
    field_simp
  have hsn : ‖s‖ ≤ 2 * |t| := by
    have : s = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      simp [hsdef, half]
    rw [this]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have hdiv : ‖F‖ ≤ 8 / (D : ℝ) * Gmax + 2 * M * Bd := by
    rw [← mul_le_mul_iff_of_pos_left hq2]
    calc (q : ℝ) ^ 2 * ‖F‖ ≤ _ := hmain
      _ = _ := by field_simp
  have ht1 : 8 / (D : ℝ) * Gmax ≤ 384 * S / t ^ 2 := by
    have h5 : Gmax ≤ 3 * x * S / t ^ 2 := by
      simp only [hGmaxdef]
      exact div_le_div_of_nonneg_right h3 ht2.le
    have h6 : 8 / (D : ℝ) ≤ 128 / x := by
      rw [div_le_div_iff₀ hDR hx0]
      linarith
    calc 8 / (D : ℝ) * Gmax ≤ 128 / x * (3 * x * S / t ^ 2) :=
          mul_le_mul h6 h5 hGmax0 (by positivity)
      _ = 384 * S / t ^ 2 := by field_simp; ring
  have ht3 : 2 * M * Bd ≤ 64 * q * |t| / S := by
    simp only [hBd, h4]
    have hMs : (M : ℝ) * ‖s‖ ≤ 2 * x * (2 * |t|) :=
      mul_le_mul hMR hsn (norm_nonneg _) (by positivity)
    calc 2 * M * (‖s‖ * (8 / (x * S)) * q) = 2 * ((M : ℝ) * ‖s‖) * (8 / (x * S)) * q := by ring
      _ ≤ 2 * (2 * x * (2 * |t|)) * (8 / (x * S)) * q := by gcongr
      _ = 64 * q * |t| / S := by field_simp; ring
  linarith

/-- The elementary integral bound behind the mean value hypothesis. -/
theorem integral_bound {f : ℝ → ℝ} {a b A B : ℝ} (hf0 : ∀ t, 0 ≤ f t) (ha : 0 < a) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : ∀ t ∈ Set.Icc a b, f t ≤ A / t ^ 2 + B) :
    ∫ t in a..b, f t ≤ A / a + B * b := by
  have hR : 0 ≤ A / a + B * b := by positivity
  by_cases hab : a ≤ b
  · by_cases hi : IntervalIntegrable f MeasureTheory.volume a b
    · have hg : IntervalIntegrable (fun t : ℝ => A / t ^ 2 + B) MeasureTheory.volume a b := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hab]
        apply ContinuousOn.add _ continuousOn_const
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro t ht
        have : 0 < t := ha.trans_le ht.1
        positivity
      have h1 := intervalIntegral.integral_mono_on hab hi hg hp
      have h2 : ∫ t in a..b, (A / t ^ 2 + B) = (-A / b + B * b) - (-A / a + B * a) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -A / t + B * t) _ hg
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
        have d1 := (hasDerivAt_inv ht0).const_mul (-A)
        have d2 := (hasDerivAt_id t).const_mul B
        convert d1.add d2 using 1
        · funext z; simp [div_eq_mul_inv]
        · simp; field_simp
      have hbp : 0 < b := ha.trans_le hab
      have : 0 ≤ A / b := by positivity
      have h3 : 0 ≤ B * a := by positivity
      rw [neg_div, neg_div] at h2
      linarith
    · rw [intervalIntegral.integral_undef hi]; exact hR
  · have hba : b ≤ a := (not_le.mp hab).le
    rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_nonneg hba (fun u _ => hf0 u) (μ := MeasureTheory.volume)
    linarith

theorem ev_bounds {A : ℝ} (hA : 0 < A) : ∃ X1 : ℝ, ∀ x, X1 ≤ x →
    64 ≤ x ∧ 1 ≤ L x ∧ L x ^ A ≤ T0 x ∧ 64 * L x ^ (2 * A) ≤ x ^ (0.1 : ℝ) := by
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, 64 ≤ x := Filter.eventually_ge_atTop 64
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e3 := (isLittleO_log_rpow_rpow_atTop (2 * A) (by norm_num : (0 : ℝ) < 0.1)).def
    (by norm_num : (0 : ℝ) < 1 / 64)
  have ey : Filter.Tendsto (fun x : ℝ => Real.log x ^ (1 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp Real.tendsto_log_atTop
  have e4 : ∀ᶠ y : ℝ in Filter.atTop, 1 ≤ Real.exp y / y ^ (3 * A) :=
    (tendsto_exp_div_rpow_atTop (3 * A)).eventually_ge_atTop 1
  have e5 : ∀ᶠ y : ℝ in Filter.atTop, 0 < y := Filter.eventually_gt_atTop 0
  have e6 := ey.eventually (e4.and e5)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and e6)))
  refine ⟨X1, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hX1 x hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  refine ⟨h1, h2, ?_, ?_⟩
  · have hy := (one_le_div (Real.rpow_pos_of_pos h5 _)).mp h4
    have : (Real.log x ^ (1 / 3 : ℝ)) ^ (3 * A) = Real.log x ^ A := by
      rw [← Real.rpow_mul hL0.le]
      congr 1
      ring
    rw [this] at hy
    exact hy
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at h3
    simp only [L]
    linarith

/-- The trapezoid satisfies the mean value hypothesis 4.1 at both signs of t, every character,
with the printed range T0 to T1. This also serves as the vacuity instance of the repaired
`Lemma11`, with positive density. -/
theorem plateau_mean {ε : ℝ} (hε : 0 ≤ ε) (σ : ℝ → ℝ) (hσ : ∀ t, |σ t| = |t|) :
    ∀ A : ℝ, 0 < A → ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∫ t in (T0 x)..(T1 ε x),
          ‖(⟨cP x, Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half (σ t))‖ ≤
          385 * x ^ (1 / 2 : ℝ) / L x ^ A := by
  intro A hA
  obtain ⟨X1, hX1⟩ := ev_bounds hA
  refine ⟨X1, fun x hx q _ hq χ => ?_⟩
  obtain ⟨h64, hL1, hLT, hLx⟩ := hX1 x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLpos : 0 < L x := by linarith
  have hLA : 0 < L x ^ A := Real.rpow_pos_of_pos hLpos _
  have hLA1 : 1 ≤ L x ^ A := Real.one_le_rpow hL1 hA.le
  have hLL : L x ^ A * L x ^ A = L x ^ (2 * A) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  set S : ℝ := x ^ (1 / 2 : ℝ) with hSdef
  have hSpos : 0 < S := by positivity
  have hSS : S * S = x := by
    rw [hSdef, ← Real.rpow_add hx0]; norm_num
  have hT0 : 1 ≤ T0 x := by
    unfold T0
    exact Real.one_le_exp (Real.rpow_nonneg hLpos.le _)
  have hT1pos : 0 < T1 ε x := by unfold T1; positivity
  have hT1le : T1 ε x ≤ x ^ (0.45 : ℝ) := by
    unfold T1
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsplit : x ^ (0.1 : ℝ) * (x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ)) = x := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hx01 : 1 ≤ x ^ (0.1 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hx045 : 1 ≤ x ^ (0.45 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hqx : (q : ℝ) ≤ x / 16 := by
    have s1 : L x ^ A ≤ L x ^ (2 * A) := by rw [← hLL]; nlinarith
    have s2 : 64 * (q : ℝ) ≤ x ^ (0.1 : ℝ) := by linarith
    have s3 : x ^ (0.1 : ℝ) ≤ x := by
      calc x ^ (0.1 : ℝ) = x ^ (0.1 : ℝ) * 1 := (mul_one _).symm
        _ ≤ x ^ (0.1 : ℝ) * (x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith
        _ = x := hsplit
    linarith
  have hb := integral_bound (a := T0 x) (b := T1 ε x) (A := 384 * S)
    (B := 64 * q * T1 ε x / S)
    (f := fun t => ‖(⟨cP x, Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half (σ t))‖)
    (fun _ => norm_nonneg _) (by linarith) hT1pos.le (by positivity) (by positivity)
    (fun t ht => by
      have ht1 : 1 ≤ t := hT0.trans ht.1
      have hat : |σ t| = t := by rw [hσ, abs_of_pos (by linarith)]
      have h := dp_bound χ h64 hqx (t := σ t) (by rw [hat]; exact ht1)
      rw [hat, ← sq_abs (σ t), hat] at h
      refine h.trans (add_le_add le_rfl ?_)
      apply div_le_div_of_nonneg_right _ hSpos.le
      exact mul_le_mul_of_nonneg_left ht.2 (by positivity))
  refine hb.trans ?_
  have g1 : 384 * S / T0 x ≤ 384 * S / L x ^ A :=
    div_le_div_of_nonneg_left (by positivity) hLA hLT
  have g2 : 64 * q * T1 ε x / S * T1 ε x ≤ S / L x ^ A := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hSpos hLA]
    have hT2 : T1 ε x * T1 ε x ≤ x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ) :=
      mul_le_mul hT1le hT1le hT1pos.le (by positivity)
    have hq2 : 64 * (q : ℝ) * L x ^ A ≤ x ^ (0.1 : ℝ) := by
      have : (q : ℝ) * L x ^ A ≤ L x ^ A * L x ^ A := mul_le_mul_of_nonneg_right hq hLA.le
      rw [hLL] at this
      linarith
    calc 64 * q * T1 ε x * T1 ε x * L x ^ A
        = (64 * (q : ℝ) * L x ^ A) * (T1 ε x * T1 ε x) := by ring
      _ ≤ x ^ (0.1 : ℝ) * (x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ)) :=
          mul_le_mul hq2 hT2 (by positivity) (by positivity)
      _ = x := hsplit
      _ = S * S := hSS.symm
  have : 385 * S / L x ^ A = 384 * S / L x ^ A + S / L x ^ A := by ring
  rw [this]
  linarith

theorem cP_norm (x : ℝ) (k : ℕ) : ‖cP x k‖ ≤ 1 := by
  by_cases hD : dX x = 0
  · simp [cP, tz, hD]
  · have hD0 : 0 < dX x := Nat.pos_of_ne_zero hD
    have hx8 : 8 ≤ x := by
      by_contra hc
      have hlt : x / 8 < 1 := by linarith [not_le.mp hc]
      have : dX x = 0 := by
        unfold dX
        exact Nat.floor_eq_zero.mpr hlt
      exact hD this
    have hab : aX x + dX x ≤ bX x := by
      apply Nat.le_floor
      have a1 : (aX x : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
      have d1 : (dX x : ℝ) ≤ x / 8 := Nat.floor_le (by linarith)
      push_cast
      linarith
    have hb := tz_bounds hD0 hab (k : ℝ)
    simp only [cP, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hb.1]
    exact hb.2

theorem cP_one {x : ℝ} (hx : 64 ≤ x) {k : ℕ} (h1 : 5 * x / 8 ≤ k) (h2 : (k : ℝ) ≤ x) :
    cP x k = 1 := by
  obtain ⟨hD, hab, ha1, ha2, hd1, hd2, hb1, hb2⟩ := params hx
  have hkb : (k : ℝ) ≤ bX x := by
    have : k ≤ bX x := Nat.le_floor h2
    exact_mod_cast this
  have := tz_one hD hab (u := (k : ℝ)) (by linarith) hkb
  simp [cP, this]

/-- Old `Holds42` fails for any family equal to 1 on [5x/8, x]. This follows the computation of
`not_holds42_constant_one`. -/
theorem not_holds42Old_of_plateau {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 20) {c : ℝ → ℕ → ℂ}
    (hc : ∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ k : ℕ, 5 * x / 8 ≤ k → (k : ℝ) ≤ x → c x k = 1) :
    ¬ Holds42Old ε c := by
  intro h
  obtain ⟨X1, hc⟩ := hc
  obtain ⟨C, X0, hC⟩ := h 1 (by norm_num)
  let T : ℝ := max 216 (max (max X0 X1) (4 * |C| + 1))
  let x : ℝ := Real.exp T
  have hT : 216 ≤ T := le_max_left _ _
  have hTX : max X0 X1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTC : 4 * |C| + 1 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := Real.exp_pos _
  have hxT : T + 1 ≤ x := Real.add_one_le_exp T
  have hxX0 : X0 ≤ x := by linarith [le_max_left X0 X1]
  have hxX1 : X1 ≤ x := by linarith [le_max_right X0 X1]
  have hlog : Real.log x = T := Real.log_exp _
  have h216 : (216 : ℝ) ^ (2 / 3 : ℝ) = 36 := by
    rw [show (216 : ℝ) = 6 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h6 : 6 ≤ T ^ (2 / 3 : ℝ) := by
    have he := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 216) hT (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [h216] at he
    linarith
  have hrootid : T ^ (1 / 3 : ℝ) * T ^ (2 / 3 : ℝ) = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have hroot : 3 * T ^ (1 / 3 : ℝ) ≤ T / 2 := by
    have he := mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hT0.le (1 / 3 : ℝ))
    nlinarith
  have hr1 : 1 ≤ T ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hY : Yof ε x = Real.exp (T * (11 / 20 + ε)) := by
    unfold Yof theta1
    rw [Real.rpow_def_of_pos hx0, hlog]
  have hy : y1 x = Real.exp (T - 3 * T ^ (1 / 3 : ℝ)) := by
    rw [y1, hlog, show x = Real.exp T from rfl, ← Real.exp_add]
    congr 1
    ring
  have hY4 : 4 ≤ Yof ε x := by
    rw [hY]
    have := Real.add_one_le_exp (T * (11 / 20 + ε))
    have heps := mul_nonneg hT0.le hε
    nlinarith
  have hy4 : 4 ≤ y1 x := by
    rw [hy]; have := Real.add_one_le_exp (T - 3 * T ^ (1 / 3 : ℝ)); linarith
  have hy0 : 0 < y1 x := by linarith
  have hY0 : 0 ≤ Yof ε x := by linarith
  have hxY6 : 6 * Yof ε x ≤ x := by
    rw [hY]
    have he : 6 ≤ Real.exp (T * (9 / 20 - ε)) := by
      have := Real.add_one_le_exp (T * (9 / 20 - ε))
      have heps := mul_le_mul_of_nonneg_left hεsmall hT0.le
      nlinarith
    calc 6 * Real.exp (T * (11 / 20 + ε)) ≤
        Real.exp (T * (9 / 20 - ε)) * Real.exp (T * (11 / 20 + ε)) :=
          mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = x := by dsimp [x]; rw [← Real.exp_add]; congr 1; ring
  have hxY : 2 * Yof ε x ≤ x := by linarith
  have hyx : y1 x ≤ x / 4 := by
    rw [y1, hlog]
    have e1 : 4 ≤ Real.exp (3 * T ^ (1 / 3 : ℝ)) := by
      have := Real.add_one_le_exp (3 * T ^ (1 / 3 : ℝ))
      linarith
    have e2 : Real.exp (-3 * T ^ (1 / 3 : ℝ)) ≤ 1 / 4 := by
      rw [show -3 * T ^ (1 / 3 : ℝ) = -(3 * T ^ (1 / 3 : ℝ)) by ring, Real.exp_neg]
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) e1
    nlinarith
  have hs := (Iset_card_bounds hY0 hxY).1
  have hlong : ((Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊).card : ℝ) ≤ y1 x + 1 := by
    have hm : ⌊x - y1 x⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
    rw [Nat.card_Ioc, Nat.cast_sub hm]
    linarith [Nat.floor_le hx0.le, Nat.lt_floor_add_one (x - y1 x)]
  have hratio : 0 ≤ Yof ε x / y1 x := div_nonneg hY0 hy0.le
  have hscaled := mul_le_mul_of_nonneg_left hlong hratio
  have hid : Yof ε x / y1 x * (y1 x + 1) = Yof ε x + Yof ε x / y1 x := by
    field_simp [hy0.ne']
  rw [hid] at hscaled
  have hratio4 : Yof ε x / y1 x ≤ Yof ε x / 4 := div_le_div_of_nonneg_left hY0 (by norm_num) hy4
  have hCT : C / T ≤ 1 / 4 := by
    apply (div_le_iff₀ hT0).mpr
    have := le_abs_self C
    linarith
  have herr : C * Yof ε x / L x ^ (1 : ℝ) ≤ Yof ε x / 4 := by
    rw [Real.rpow_one, L, hlog]
    calc C * Yof ε x / T = (C / T) * Yof ε x := by ring
      _ ≤ (1 / 4) * Yof ε x := mul_le_mul_of_nonneg_right hCT hY0
      _ = _ := by ring
  have hχ : ∀ k : ℕ, (1 : DirichletCharacter ℂ 1) (k : ZMod 1) = 1 := by
    intro k
    apply MulChar.one_apply
    exact ⟨1, Subsingleton.elim _ _⟩
  have hq1 : ((1 : ℕ) : ℝ) ≤ L x ^ (1 : ℝ) := by
    rw [Real.rpow_one, L, hlog]; push_cast; linarith
  have hI : ∑ k ∈ Iset ε x, c x k * (1 : DirichletCharacter ℂ 1) (k : ZMod 1) =
      ((Iset ε x).card : ℂ) := by
    rw [sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro k hk
      have hk' := mem_Ioc.mp hk
      have hle : (k : ℝ) ≤ x := by
        have : (k : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hk'.2
        exact this.trans (Nat.floor_le hx0.le)
      have hlo : x - 2 * Yof ε x < k :=
        (Nat.floor_lt (by linarith)).mp hk'.1
      rw [hc x hxX1 k (by linarith) hle, hχ, one_mul]
  have hI1 : ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * (1 : DirichletCharacter ℂ 1) (k : ZMod 1) =
      ((Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊).card : ℂ) := by
    rw [sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro k hk
      have hk' := mem_Ioc.mp hk
      have hle : (k : ℝ) ≤ x := by
        have : (k : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hk'.2
        exact this.trans (Nat.floor_le hx0.le)
      have hlo : x - y1 x < k :=
        (Nat.floor_lt (by linarith)).mp hk'.1
      rw [hc x hxX1 k (by linarith) hle, hχ, one_mul]
  have htransfer := hC x hxX0 1 hq1 (1 : DirichletCharacter ℂ 1)
  rw [hI, hI1] at htransfer
  have hreal : ((Iset ε x).card : ℂ) - ((Yof ε x / y1 x : ℝ) : ℂ) *
      ((Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊).card : ℂ) =
      ((((Iset ε x).card : ℝ) - Yof ε x / y1 x * ((Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊).card : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at htransfer
  have := (le_abs_self _).trans htransfer
  linarith

/-- REFUTATION, unconditional. The old `Lemma11` is false. Family `cP`, B = 0, any small ε.
Its hypotheses hold, including 4.1 for every character, and the old conclusion fails. -/
theorem lemma11Old_false : ¬ Lemma11Old := by
  rintro ⟨ε0, h0, h⟩
  have hpos : 0 < min (ε0 / 2) (1 / 20) := lt_min (by linarith) (by norm_num)
  have hlt : min (ε0 / 2) (1 / 20) < ε0 := (min_le_left _ _).trans_lt (by linarith)
  have := h _ hpos hlt 0 cP (fun x k => by simpa using cP_norm x k)
    (fun A hA => by
      obtain ⟨X0, hX⟩ := plateau_mean hpos.le id (fun _ => rfl) A hA
      exact ⟨385, X0, hX⟩)
  exact not_holds42Old_of_plateau hpos.le (min_le_right _ _)
    ⟨64, fun x hx k h1 h2 => cP_one hx h1 h2⟩ this

#print axioms plateau_mean
#print axioms not_holds42Old_of_plateau
#print axioms lemma11Old_false
end LeanLab.BakerHarmanPintz1997.Audit1617
