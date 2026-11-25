import LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

/-!
# Split of the leaf `mv_remainder_66_68`, P0015 displays (6.1) to (6.9)

Source P0015, Montgomery and Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27, 1975, 353-370, pages 355 and 358 to 363, read from the page images of
`papers/P0015.pdf`.

The chain of the proof on pages 355 and 360 to 362, each step its own theorem.
* `rem66_arc_decomp`, PROVED: `R₁(n)` is the sum over `q ≤ P` and reduced `a` of the
  integrals over the disjoint arcs `𝔐(q,a)`, page 355, and the left side of (6.4); the arc at
  `0/1` cut by `[0,1]` is glued by periodicity, integrating over `(-2P/X, 1 - 2P/X]`.
* `rem66_expand_61`, `rem66_tau_principal`, `rem66_expand_62`, `rem66_expand_64`, PROVED:
  displays (6.1) to (6.4), the character expansion of `S(a/q + η)` and the integrated square,
  with Lemma 5.2 for the principal character, `τ(χ̄₀) = μ(q)`.
* `rem66_cs_second`, `rem66_cs_third`, PROVED: display (6.6), Cauchy Schwarz together with
  `W(χ,η) = W(χ*,η)` and `1/(qQ) ≤ 1/(rQ)`.
* `rem66_T_L2`, PROVED: display (6.7), `∫_{-1/qQ}^{1/qQ} |T|² ≤ X`.
* `rem66_group_by_primitive`, PROVED: the grouping of characters by the primitive character
  inducing them.
* `rem66_group_second_of`, `rem66_group_third_of`, PROVED from Lemma 5.5: display (6.8).
* LEAF `rem66_lemma55`: Lemma 5.5, display (5.4), page 360, class HARD. The only sorry.
* `rem66_of_lemma55`, PROVED sorry free with Lemma 5.5 as a hypothesis, and `rem66_of_leaves`,
  the exact statement of `Lemma2MVSplit.mv_remainder_66_68`, so that leaf is CONDITIONAL ON
  `rem66_lemma55` alone.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1 eC Sp majorArcs)

/-! ### Definitions, each a display of P0015 -/

/-- P0015 display (2.1), page 355: `c_χ(m) = Σ_{h=1}^{q} χ(h) e(hm/q)`, here with `h` running
over `0 ≤ h < q`, the same residues; the Gauss sum is `τ(χ) = c_χ(1)`. -/
noncomputable def rem66_cchi {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℤ) : ℂ :=
  ∑ h ∈ range q, χ (h : ZMod q) * eC ((h : ℝ) * m / q)

/-- The left side of P0015 display (6.4), page 362: `Σ'_a ∫_{𝔐(q,a)} S(α)² e(-nα) dα`, written
with `α = a/q + η`, `|η| ≤ 1/(qQ) = P/(qX)`, and `a` over the reduced residues `0 ≤ a < q`. -/
noncomputable def rem66_arcSum (P X : ℝ) (q n : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ η in (-(P / (q * X)))..(P / (q * X)),
      Sp P X ((a : ℝ) / q + η) ^ 2 * eC (-(((a : ℝ) / q + η) * n))

/-- The second term of P0015 display (6.4), page 362:
`2 μ(q) φ(q)⁻² Σ_χ c_χ(-n) τ(χ̄) ∫_{-1/qQ}^{1/qQ} T(η) W(χ,η) e(-nη) dη`. -/
noncomputable def rem66_second (P X : ℝ) (q n : ℕ) : ℂ :=
  2 * ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((q.totient : ℂ) ^ 2) *
    ∑ᶠ χ : DirichletCharacter ℂ q, rem66_cchi χ (-(n : ℤ)) * rem66_cchi χ⁻¹ 1 *
      ∫ η in (-(P / (q * X)))..(P / (q * X)), T P X η * Wchi P X χ η * eC (-(η * n))

/-- The third term of P0015 display (6.4), page 362:
`φ(q)⁻² Σ_{χ,χ'} c_{χχ'}(-n) τ(χ̄) τ(χ̄') ∫_{-1/qQ}^{1/qQ} W(χ,η) W(χ',η) e(-nη) dη`. -/
noncomputable def rem66_third (P X : ℝ) (q n : ℕ) : ℂ :=
  1 / ((q.totient : ℂ) ^ 2) *
    ∑ᶠ χ : DirichletCharacter ℂ q, ∑ᶠ χ' : DirichletCharacter ℂ q,
      rem66_cchi (χ * χ') (-(n : ℤ)) * rem66_cchi χ⁻¹ 1 * rem66_cchi χ'⁻¹ 1 *
        ∫ η in (-(P / (q * X)))..(P / (q * X)), Wchi P X χ η * Wchi P X χ' η * eC (-(η * n))

/-- The `q` term of the first sum of P0015 display (6.6), page 362, without the factor `2X^{1/2}`:
`μ(q)² φ(q)⁻² Σ_χ |c_χ(-n) τ(χ̄)| W(χ*)`, with `χ*` the primitive character inducing `χ`. -/
noncomputable def rem66_A2 (P X : ℝ) (q n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
    ∑ᶠ χ : DirichletCharacter ℂ q,
      ‖rem66_cchi χ (-(n : ℤ)) * rem66_cchi χ⁻¹ 1‖ * Wnorm P X χ.primitiveCharacter

/-- The `q` term of the second sum of P0015 display (6.6), page 362:
`φ(q)⁻² Σ_{χ,χ'} |c_{χχ'}(-n) τ(χ̄) τ(χ̄')| W(χ*) W(χ'*)`. -/
noncomputable def rem66_A3 (P X : ℝ) (q n : ℕ) : ℝ :=
  1 / (q.totient : ℝ) ^ 2 *
    ∑ᶠ χ : DirichletCharacter ℂ q, ∑ᶠ χ' : DirichletCharacter ℂ q,
      ‖rem66_cchi (χ * χ') (-(n : ℤ)) * rem66_cchi χ⁻¹ 1 * rem66_cchi χ'⁻¹ 1‖ *
        Wnorm P X χ.primitiveCharacter * Wnorm P X χ'.primitiveCharacter

/-! ### Display (6.7), proved -/

/-- `conj e(x) = e(-x)`, used for `|T(η)|²` in P0015 display (6.7), page 362. -/
lemma rem66_eC_conj (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

/-- `e(x+y) = e(x) e(y)`, used in P0015 displays (6.1) and (6.7), pages 361 and 362. -/
lemma rem66_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `e` is continuous, for the integrals of P0015 display (6.7), page 362. -/
lemma rem66_continuous_eC : Continuous eC := by
  unfold eC; fun_prop

/-- `e(m) = 1` for an integer `m`, the periodicity behind P0015 display (6.7), page 362. -/
lemma rem66_eC_int (m : ℤ) : eC m = 1 := by
  unfold eC
  have : 2 * (π : ℂ) * Complex.I * ((m : ℝ) : ℂ) = m * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- `∫_0^1 e(kη) dη = [k = 0]`, the orthogonality behind P0015 display (6.7), page 362. -/
lemma rem66_integral_eC_int (k : ℤ) :
    ∫ α in (0 : ℝ)..1, eC (k * α) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]
  · have hc : (2 * (π : ℂ) * Complex.I * k) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have h1 : (fun α : ℝ => eC (k * α)) =
        fun α : ℝ => Complex.exp ((2 * (π : ℂ) * Complex.I * k) * α) := by
      funext α; unfold eC; congr 1; push_cast; ring
    rw [h1, integral_exp_mul_complex hc]
    have h2 : Complex.exp (2 * (π : ℂ) * Complex.I * k) = 1 := by
      have := rem66_eC_int k; unfold eC at this; rw [← this]; congr 1
    simp [h2]

/-- `|T(η)|²` has period `1`, P0015 display (6.7), page 362. -/
lemma rem66_T_periodic (P X : ℝ) : Function.Periodic (fun η => ‖T P X η‖ ^ 2) 1 := by
  intro η
  simp only [T]
  congr 2
  refine sum_congr rfl (fun m _ => ?_)
  rw [add_mul, one_mul, rem66_eC_add]
  rw [show eC (m : ℝ) = 1 from by exact_mod_cast rem66_eC_int (m : ℤ), mul_one]

/-- `T` is continuous, P0015 page 361. -/
lemma rem66_T_cont (P X : ℝ) : Continuous (fun η => T P X η) := by
  unfold T
  have := rem66_continuous_eC
  fun_prop

/-- Parseval for `T`, P0015 display (6.7), page 362: `∫_0^1 |T(η)|² dη = Σ_{P<n≤X} 1`. -/
lemma rem66_T_parseval (P X : ℝ) :
    ∫ η in (0 : ℝ)..1, ‖T P X η‖ ^ 2 = ((Ioc ⌊P⌋₊ ⌊X⌋₊).card : ℝ) := by
  set I := Ioc ⌊P⌋₊ ⌊X⌋₊
  have hpt : ∀ η : ℝ, ((‖T P X η‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ I, ∑ k ∈ I, eC ((((m : ℤ) - k : ℤ) : ℝ) * η) := by
    intro η
    push_cast
    rw [← Complex.mul_conj', T, map_sum, sum_mul_sum]
    refine sum_congr rfl (fun m _ => sum_congr rfl (fun k _ => ?_))
    rw [rem66_eC_conj, ← rem66_eC_add]; congr 1; ring
  have hc : ((∫ η in (0 : ℝ)..1, ‖T P X η‖ ^ 2 : ℝ) : ℂ) = (I.card : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hpt]
    have hint : ∀ m k : ℕ, IntervalIntegrable
        (fun η : ℝ => eC ((((m : ℤ) - k : ℤ) : ℝ) * η)) MeasureTheory.volume 0 1 := by
      intro m k
      have := rem66_continuous_eC
      exact (by fun_prop : Continuous (fun η : ℝ => eC ((((m : ℤ) - k : ℤ) : ℝ) * η))).intervalIntegrable 0 1
    rw [intervalIntegral.integral_finsetSum (fun m _ => by
      have := rem66_continuous_eC
      exact (by fun_prop : Continuous (fun η : ℝ => ∑ k ∈ I, eC ((((m : ℤ) - k : ℤ) : ℝ) * η))).intervalIntegrable 0 1)]
    simp_rw [intervalIntegral.integral_finsetSum (fun k _ => hint _ k), rem66_integral_eC_int]
    simp [sub_eq_zero]
  exact_mod_cast hc

/-- P0015 display (6.7), page 362, PROVED.
`∫_{-1/qQ}^{1/qQ} |T(η)|² dη ≤ ∫_0^1 |T(η)|² dη = Σ_{P<n≤X} 1 ≤ X`, for `2/(qQ) ≤ 1`. -/
theorem rem66_T_L2 (P X : ℝ) (q : ℕ) (hq : 1 ≤ q) (hP : 0 ≤ P) (hX : 0 < X) (hPX : 2 * P ≤ X) :
    ∫ η in (-(P / (q * X)))..(P / (q * X)), ‖T P X η‖ ^ 2 ≤ X := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ha0 : 0 ≤ P / (q * X) := by positivity
  have ha : P / (q * X) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hcont : Continuous (fun η => ‖T P X η‖ ^ 2) := by
    have := rem66_T_cont P X; fun_prop
  calc ∫ η in (-(P / (q * X)))..(P / (q * X)), ‖T P X η‖ ^ 2
      ≤ ∫ η in (-(1 / 2 : ℝ))..(1 / 2), ‖T P X η‖ ^ 2 := by
        refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) ha ?_
          (hcont.intervalIntegrable _ _)
        exact Filter.Eventually.of_forall (fun η => by positivity)
    _ = ∫ η in (0 : ℝ)..1, ‖T P X η‖ ^ 2 := by
        have := (rem66_T_periodic P X).intervalIntegral_add_eq (-(1 / 2)) 0
        norm_num at this ⊢
        exact this
    _ = ((Ioc ⌊P⌋₊ ⌊X⌋₊).card : ℝ) := rem66_T_parseval P X
    _ ≤ X := by
        rw [Nat.card_Ioc]
        calc ((⌊X⌋₊ - ⌊P⌋₊ : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
          _ ≤ X := Nat.floor_le hX.le

/-! ### Display (6.6), proved -/

/-- `|e(x)| = 1`, used in the Cauchy Schwarz step of P0015 display (6.6), page 362. -/
lemma rem66_norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- P0015 page 361, the harmless condition `p > P`: for `q ≤ P` every prime `p > P` is prime to
`q`, so `W(χ,η) = W(χ*,η)` with `χ*` the primitive character inducing `χ`. PROVED. -/
lemma rem66_wchi_primitive (P X : ℝ) {q : ℕ} (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P)
    (χ : DirichletCharacter ℂ q) (η : ℝ) :
    Wchi P X χ η = Wchi P X χ.primitiveCharacter η := by
  have : NeZero q := ⟨by omega⟩
  have hone : χ = 1 ↔ χ.primitiveCharacter = 1 := by
    conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
    have : NeZero q := ⟨by omega⟩
    exact DirichletCharacter.changeLevel_eq_one_iff _
  have hS : Schi P X χ η = Schi P X χ.primitiveCharacter η := by
    unfold Schi
    refine sum_congr rfl (fun p hp => ?_)
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have hPp : ⌊P⌋₊ < p := (mem_Ioc.mp hpI).1
    have hqf : q ≤ ⌊P⌋₊ := Nat.le_floor hqP
    have hcop : Nat.Coprime p q := by
      rw [Nat.Prime.coprime_iff_not_dvd hpp]
      intro hd; have := Nat.le_of_dvd (by omega) hd; omega
    have hic : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    have := χ.primitiveCharacter_apply_of_isCoprime hic
    push_cast at this
    rw [this]
  unfold Wchi
  rw [hS]
  by_cases h : χ = 1
  · simp only [h, hone.mp h, ite_true]
  · have h' : ¬ χ.primitiveCharacter = 1 := fun h' => h (hone.mpr h')
    simp only [h, h', ite_false]

/-- `W(χ,η)` is continuous in `η`, P0015 page 361. -/
lemma rem66_wchi_cont (P X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (fun η => Wchi P X χ η) := by
  unfold Wchi Schi
  have := rem66_continuous_eC
  have := rem66_T_cont P X
  split_ifs <;> fun_prop

/-- The Cauchy Schwarz inequality on an interval, used in P0015 display (6.6), page 362. -/
lemma rem66_cs_real (a b : ℝ) (hab : a ≤ b) (u v : ℝ → ℝ) (hu : Continuous u)
    (hv : Continuous v) :
    ∫ x in a..b, u x * v x ≤
      Real.sqrt (∫ x in a..b, u x ^ 2) * Real.sqrt (∫ x in a..b, v x ^ 2) := by
  set A := ∫ x in a..b, u x ^ 2
  set B := ∫ x in a..b, v x ^ 2
  set C := ∫ x in a..b, u x * v x
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
  have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * C + B := by
    intro t
    have h0 : 0 ≤ ∫ x in a..b, (t * u x - v x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : ∫ x in a..b, (t * u x - v x) ^ 2 = t ^ 2 * A - 2 * t * C + B := by
      have e : (fun x => (t * u x - v x) ^ 2) =
          fun x => (t ^ 2 * u x ^ 2 - 2 * t * (u x * v x)) + v x ^ 2 := by
        funext x; ring
      rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _
    linarith [hexp ▸ h0]
  have hC2 : C ^ 2 ≤ A * B := by
    rcases hA.lt_or_eq with hA' | hA'
    · have := hquad (C / A)
      have e : (C / A) ^ 2 * A - 2 * (C / A) * C + B = B - C ^ 2 / A := by
        field_simp; ring
      rw [e, sub_nonneg, div_le_iff₀ hA'] at this
      linarith
    · by_contra hcon
      have hC0 : C ≠ 0 := by
        intro h; rw [h, ← hA'] at hcon; simp at hcon
      have := hquad ((B + 1) / C)
      rw [← hA'] at this
      have e : ((B + 1) / C) ^ 2 * 0 - 2 * ((B + 1) / C) * C + B = -B - 2 := by
        field_simp; ring
      rw [e] at this
      linarith
  calc C ≤ |C| := le_abs_self C
    _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
    _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hC2
    _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B

/-- Cauchy Schwarz for `∫ f g e(-nη) dη`, the form used in P0015 display (6.6), page 362. -/
lemma rem66_cs_complex (a b : ℝ) (hab : a ≤ b) (f g : ℝ → ℂ) (hf : Continuous f)
    (hg : Continuous g) (n : ℕ) :
    ‖∫ η in a..b, f η * g η * eC (-(η * n))‖ ≤
      Real.sqrt (∫ η in a..b, ‖f η‖ ^ 2) * Real.sqrt (∫ η in a..b, ‖g η‖ ^ 2) := by
  calc ‖∫ η in a..b, f η * g η * eC (-(η * n))‖
      ≤ ∫ η in a..b, ‖f η * g η * eC (-(η * n))‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ η in a..b, ‖f η‖ * ‖g η‖ := by
        refine intervalIntegral.integral_congr (fun η _ => ?_)
        simp only [norm_mul, rem66_norm_eC, mul_one]
    _ ≤ _ := rem66_cs_real a b hab _ _ (by fun_prop) (by fun_prop)

/-- P0015 display (6.5) and page 362: for the conductor `r ∣ q`, `1/(qQ) ≤ 1/(rQ)`, so
`(∫_{-1/qQ}^{1/qQ} |W(χ,η)|² dη)^{1/2} ≤ W(χ*)`, using `W(χ,η) = W(χ*,η)`. -/
lemma rem66_wnorm_mono (P X : ℝ) {q : ℕ} (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P) (hX : 0 < X)
    (χ : DirichletCharacter ℂ q) :
    Real.sqrt (∫ η in (-(P / (q * X)))..(P / (q * X)), ‖Wchi P X χ η‖ ^ 2) ≤
      Wnorm P X χ.primitiveCharacter := by
  have : NeZero q := ⟨by omega⟩
  unfold Wnorm
  apply Real.sqrt_le_sqrt
  have hr : 1 ≤ χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hrq : χ.conductor ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hP : 0 < P := lt_of_lt_of_le (by exact_mod_cast hq) hqP
  have hr1 : (1 : ℝ) ≤ χ.conductor := by exact_mod_cast hr
  have hrq' : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hrq
  have ha0 : 0 ≤ P / (q * X) := by positivity
  have hle : P / (q * X) ≤ P / (χ.conductor * X) := by
    apply div_le_div_of_nonneg_left hP.le (by positivity)
    exact mul_le_mul_of_nonneg_right hrq' hX.le
  have hcont : Continuous (fun η => ‖Wchi P X χ.primitiveCharacter η‖ ^ 2) := by
    have := rem66_wchi_cont P X χ.primitiveCharacter; fun_prop
  have heq : (fun η => ‖Wchi P X χ η‖ ^ 2) =
      fun η => ‖Wchi P X χ.primitiveCharacter η‖ ^ 2 := by
    funext η; rw [rem66_wchi_primitive P X hq hqP χ η]
  rw [heq]
  refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) hle ?_
    (hcont.intervalIntegrable _ _)
  exact Filter.Eventually.of_forall (fun η => by positivity)

/-- P0015 display (6.6), page 362, the first sum, PROVED. Cauchy Schwarz on
`∫ T(η) W(χ,η) e(-nη) dη`, together with `W(χ,η) = W(χ*,η)` for primes `p > P ≥ q`,
`1/(qQ) ≤ 1/(rQ)` for the conductor `r ∣ q`, and `|μ(q)| = μ(q)²`. -/
theorem rem66_cs_second (P X : ℝ) (q n : ℕ) (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P) (hX : 0 < X) :
    ‖rem66_second P X q n‖ ≤
      2 * Real.sqrt (∫ η in (-(P / (q * X)))..(P / (q * X)), ‖T P X η‖ ^ 2) *
        rem66_A2 P X q n := by
  classical
  have : NeZero q := ⟨by omega⟩
  letI := Fintype.ofFinite (DirichletCharacter ℂ q)
  have hP : 0 < P := lt_of_lt_of_le (by exact_mod_cast hq) hqP
  have ha : -(P / (q * X)) ≤ P / (q * X) := by
    have : 0 ≤ P / (q * X) := by positivity
    linarith
  set T2 := Real.sqrt (∫ η in (-(P / (q * X)))..(P / (q * X)), ‖T P X η‖ ^ 2)
  have hT2 : 0 ≤ T2 := Real.sqrt_nonneg _
  have hI : ∀ χ : DirichletCharacter ℂ q,
      ‖∫ η in (-(P / (q * X)))..(P / (q * X)), T P X η * Wchi P X χ η * eC (-(η * n))‖ ≤
        T2 * Wnorm P X χ.primitiveCharacter := fun χ =>
    (rem66_cs_complex _ _ ha _ _ (rem66_T_cont P X) (rem66_wchi_cont P X χ) n).trans
      (mul_le_mul_of_nonneg_left (rem66_wnorm_mono P X hq hqP hX χ) hT2)
  have habs : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| =
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 := by
    rw [← Int.cast_abs, ← Int.cast_pow, ArithmeticFunction.abs_moebius,
      ArithmeticFunction.moebius_sq]
  have hmu : ‖(2 * ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((q.totient : ℂ) ^ 2))‖ =
      2 * (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_intCast, habs]
    norm_num
    ring
  unfold rem66_second rem66_A2
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, norm_mul, hmu]
  calc 2 * (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        ‖∑ χ : DirichletCharacter ℂ q, rem66_cchi χ (-(n : ℤ)) * rem66_cchi χ⁻¹ 1 *
          ∫ η in (-(P / (q * X)))..(P / (q * X)), T P X η * Wchi P X χ η * eC (-(η * n))‖
      ≤ 2 * (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        ∑ χ : DirichletCharacter ℂ q, ‖rem66_cchi χ (-(n : ℤ)) * rem66_cchi χ⁻¹ 1‖ *
          (T2 * Wnorm P X χ.primitiveCharacter) := by
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum (fun χ _ => ?_))
        rw [norm_mul (rem66_cchi χ (-(n : ℤ)) * rem66_cchi χ⁻¹ 1)]
        exact mul_le_mul_of_nonneg_left (hI χ) (norm_nonneg _)
    _ = _ := by
        simp only [mul_sum]
        refine sum_congr rfl (fun χ _ => by ring)

/-- P0015 display (6.6), page 362, the second sum, PROVED. Cauchy Schwarz on
`∫ W(χ,η) W(χ',η) e(-nη) dη`, with `W(χ,η) = W(χ*,η)` and `1/(qQ) ≤ 1/(rQ)`. -/
theorem rem66_cs_third (P X : ℝ) (q n : ℕ) (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P) (hX : 0 < X) :
    ‖rem66_third P X q n‖ ≤ rem66_A3 P X q n := by
  classical
  have : NeZero q := ⟨by omega⟩
  letI := Fintype.ofFinite (DirichletCharacter ℂ q)
  have hP : 0 < P := lt_of_lt_of_le (by exact_mod_cast hq) hqP
  have ha : -(P / (q * X)) ≤ P / (q * X) := by
    have : 0 ≤ P / (q * X) := by positivity
    linarith
  have hI : ∀ χ χ' : DirichletCharacter ℂ q,
      ‖∫ η in (-(P / (q * X)))..(P / (q * X)), Wchi P X χ η * Wchi P X χ' η * eC (-(η * n))‖ ≤
        Wnorm P X χ.primitiveCharacter * Wnorm P X χ'.primitiveCharacter := fun χ χ' =>
    (rem66_cs_complex _ _ ha _ _ (rem66_wchi_cont P X χ) (rem66_wchi_cont P X χ') n).trans
      (mul_le_mul (rem66_wnorm_mono P X hq hqP hX χ) (rem66_wnorm_mono P X hq hqP hX χ')
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hphi : ‖(1 / ((q.totient : ℂ) ^ 2))‖ = 1 / (q.totient : ℝ) ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_natCast, norm_one]
  unfold rem66_third rem66_A3
  simp only [finsum_eq_sum_of_fintype]
  rw [norm_mul, hphi]
  gcongr
  refine (norm_sum_le _ _).trans (sum_le_sum (fun χ _ => ?_))
  refine (norm_sum_le _ _).trans (sum_le_sum (fun χ' _ => ?_))
  rw [norm_mul (rem66_cchi (χ * χ') (-(n : ℤ)) * rem66_cchi χ⁻¹ 1 * rem66_cchi χ'⁻¹ 1)]
  exact (mul_le_mul_of_nonneg_left (hI χ χ') (norm_nonneg (rem66_cchi (χ * χ') (-(n : ℤ)) *
    rem66_cchi χ⁻¹ 1 * rem66_cchi χ'⁻¹ 1))).trans (le_of_eq (by ring))

/-! ### Displays (6.1) to (6.4) -/

/-- Orthogonality of the characters mod `q`, used for P0015 page 361 before (6.1):
`Σ_χ χ̄(h) χ(b) = φ(q)` if `h = b` and `0` otherwise, for a unit `b`. -/
lemma rem66_char_orth {q : ℕ} [NeZero q] (h : ZMod q) {b : ZMod q} (hb : IsUnit b) :
    ∑ χ : DirichletCharacter ℂ q, χ⁻¹ h * χ b = if h = b then (q.totient : ℂ) else 0 := by
  by_cases hh : IsUnit h
  · have hinv : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ h = χ h⁻¹ := by
      intro χ
      rw [MulChar.inv_apply_eq_inv']
      have h1 : χ h * χ h⁻¹ = 1 := by
        rw [← map_mul, ZMod.mul_inv_of_unit h hh, map_one]
      exact inv_eq_of_mul_eq_one_right h1
    simp_rw [hinv]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hh b
  · have h0 : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ h = 0 := by
      intro χ; rw [MulChar.inv_apply_eq_inv', χ.map_nonunit hh, inv_zero]
    simp only [h0, zero_mul, sum_const_zero]
    rw [ite_eq_right_iff.mpr]; rintro rfl; exact absurd hb hh

/-- P0015 page 361, the display before (6.1), PROVED: for `b` prime to `q`,
`e(b/q) = φ(q)⁻¹ Σ_χ χ(b) τ(χ̄)`, used with `b = pa`. -/
theorem rem66_expand_61 (q : ℕ) (hq : 1 ≤ q) (b : ℕ) (hb : Nat.Coprime b q) :
    eC ((b : ℝ) / q) =
      1 / (q.totient : ℂ) * ∑ χ : DirichletCharacter ℂ q, χ (b : ZMod q) * rem66_cchi χ⁻¹ 1 := by
  have : NeZero q := ⟨by omega⟩
  have hφ : (q.totient : ℂ) ≠ 0 := by
    have := Nat.totient_pos.mpr (show 0 < q by omega); exact_mod_cast this.ne'
  have hbu : IsUnit (b : ZMod q) := (ZMod.isUnit_iff_coprime b q).mpr hb
  unfold rem66_cchi
  have hin : ∀ h ∈ range q, ∑ χ : DirichletCharacter ℂ q,
      χ (b : ZMod q) * (χ⁻¹ (h : ZMod q) * eC ((h : ℝ) * ((1 : ℤ) : ℝ) / q)) =
      (if h = b % q then (q.totient : ℂ) else 0) * eC ((h : ℝ) / q) := by
    intro h hh
    have hlt : h < q := mem_range.mp hh
    rw [show (fun χ : DirichletCharacter ℂ q =>
        χ (b : ZMod q) * (χ⁻¹ (h : ZMod q) * eC ((h : ℝ) * ((1 : ℤ) : ℝ) / q))) =
        fun χ => (χ⁻¹ (h : ZMod q) * χ (b : ZMod q)) * eC ((h : ℝ) / q) by
      funext χ; push_cast; ring_nf]
    rw [← sum_mul, rem66_char_orth _ hbu]
    congr 1
    have : ((h : ZMod q) = (b : ZMod q)) ↔ h = b % q := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt]
    simp only [this]
  have hsum : ∑ χ : DirichletCharacter ℂ q, χ (b : ZMod q) *
      ∑ h ∈ range q, χ⁻¹ (h : ZMod q) * eC ((h : ℝ) * ((1 : ℤ) : ℝ) / q) =
      ∑ h ∈ range q, ∑ χ : DirichletCharacter ℂ q,
        χ (b : ZMod q) * (χ⁻¹ (h : ZMod q) * eC ((h : ℝ) * ((1 : ℤ) : ℝ) / q)) := by
    simp_rw [mul_sum]; exact sum_comm
  rw [hsum, sum_congr rfl hin]
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq' (range q) (b % q)]
  simp only [mem_range, Nat.mod_lt b (show 0 < q by omega), ite_true]
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hφ, one_mul]
  have hdiv : (b : ℝ) / q = ((b / q : ℕ) : ℝ) + ((b % q : ℕ) : ℝ) / q := by
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hb' : (b : ℝ) = ((b / q : ℕ) : ℝ) * q + ((b % q : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod' b q).symm
    rw [hb']
    field_simp
  rw [hdiv, rem66_eC_add]
  rw [show eC ((b / q : ℕ) : ℝ) = 1 from by exact_mod_cast rem66_eC_int ((b / q : ℕ) : ℤ), one_mul]

/-- `Σ_{k<m} e(k/m) = [m = 1]`, used for Lemma 5.2 of P0015, page 358. -/
lemma rem66_geom (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range m, eC ((k : ℝ) / m) = if m = 1 then 1 else 0 := by
  split_ifs with h1
  · subst h1; simp [eC]
  · have hm0 : m ≠ 0 := by omega
    have hz := Complex.isPrimitiveRoot_exp m hm0
    have hk : ∀ k : ℕ, eC ((k : ℝ) / m) = (Complex.exp (2 * π * Complex.I / m)) ^ k := by
      intro k
      rw [← Complex.exp_nat_mul]; unfold eC; congr 1; push_cast; ring
    simp_rw [hk]
    exact hz.geom_sum_eq_zero (by omega)

/-- `Σ_{d ∣ g} μ(d) = [g = 1]`, used for Lemma 5.2 of P0015, page 358. -/
lemma rem66_sum_moebius (g : ℕ) :
    ∑ d ∈ g.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f g) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h2 : ((∑ d ∈ g.divisors, ArithmeticFunction.moebius d : ℤ) : ℂ) =
      ((if g = 1 then 1 else 0 : ℤ) : ℂ) := by rw [h]
  push_cast at h2
  exact h2

/-- `Σ_{h<q, d ∣ h} e(h/q) = [d = q]` for `d ∣ q`, used for Lemma 5.2 of P0015, page 358. -/
lemma rem66_dvd_sum (q d : ℕ) (hq : 1 ≤ q) (hd : d ∣ q) :
    ∑ h ∈ (range q).filter (fun h => d ∣ h), eC ((h : ℝ) / q) = if d = q then 1 else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hm0 : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have e1 : ∑ h ∈ (range (d * m)).filter (fun h => d ∣ h), eC ((h : ℝ) / (d * m : ℕ)) =
      ∑ k ∈ range m, eC ((k : ℝ) / m) := by
    symm
    refine Finset.sum_nbij (fun k => d * k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [mem_filter, mem_range]
      rw [mem_range] at hk
      exact ⟨Nat.mul_lt_mul_of_pos_left hk hd0, dvd_mul_right d k⟩
    · intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hd0 hab
    · intro h hh
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hh
      obtain ⟨hlt, k, rfl⟩ := hh
      refine ⟨k, ?_, rfl⟩
      simp only [mem_coe, mem_range]
      exact Nat.lt_of_mul_lt_mul_left hlt
    · intro k _
      congr 1
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      push_cast; field_simp
  rw [e1, rem66_geom m hm0]
  congr 1
  apply propext
  constructor
  · rintro rfl; simp
  · intro h; exact (Nat.mul_eq_left hd0.ne').mp h.symm |> fun h' => by omega

/-- P0015 Lemma 5.2, page 358, for the principal character, PROVED.
`τ(χ̄₀) = c_q(1) = μ(q)`, the case `r = 1` of Lemma 5.2, equally (5.2) with `m = 1`; by
`Σ_{d ∣ (h,q)} μ(d) = [(h,q) = 1]` and `Σ_{k<m} e(k/m) = [m = 1]`. -/
theorem rem66_tau_principal (q : ℕ) (hq : 1 ≤ q) :
    rem66_cchi (1 : DirichletCharacter ℂ q)⁻¹ 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have : NeZero q := ⟨by omega⟩
  rw [inv_one]
  unfold rem66_cchi
  have h1 : ∀ h ∈ range q, (1 : DirichletCharacter ℂ q) (h : ZMod q) *
      eC ((h : ℝ) * ((1 : ℤ) : ℝ) / q) =
      ∑ d ∈ (Nat.gcd h q).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * eC ((h : ℝ) / q) := by
    intro h _
    rw [← sum_mul, rem66_sum_moebius]
    have e : eC ((h : ℝ) * ((1 : ℤ) : ℝ) / q) = eC ((h : ℝ) / q) := by push_cast; rw [mul_one]
    rw [e]
    by_cases hc : Nat.Coprime h q
    · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime h q).mpr hc)]
      have hc' : Nat.gcd h q = 1 := hc
      simp [hc']
    · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
      have hc' : Nat.gcd h q ≠ 1 := hc
      simp [hc']
  rw [sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := q.divisors) (s' := fun d => (range q).filter (fun h => d ∣ h))]
  · simp_rw [← mul_sum]
    rw [sum_congr rfl (fun d hd => by rw [rem66_dvd_sum q d hq (Nat.dvd_of_mem_divisors hd)])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' q.divisors q]
    simp only [Nat.mem_divisors, dvd_refl, ne_eq, true_and]
    rw [if_pos (by omega)]
  · intro h d
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    have hg : Nat.gcd h q ≠ 0 := (Nat.gcd_pos_of_pos_right h (by omega)).ne'
    constructor
    · rintro ⟨hh, ⟨hdh, hdq⟩, _⟩; exact ⟨⟨hh, hdh⟩, hdq, by omega⟩
    · rintro ⟨⟨hh, hdh⟩, hdq, _⟩; exact ⟨hh, ⟨hdh, hdq⟩, hg⟩

/-- P0015 displays (6.1) and (6.2), page 361, PROVED from the expansion of `e(pa/q)` and
Lemma 5.2. Since every prime `p > P ≥ q` is prime to `q`,
`S(a/q + η) = φ(q)⁻¹ Σ_χ χ(a) τ(χ̄) S(χ,η)`, (6.1); then `S(χ₀,η) = T(η) + W(χ₀,η)` and
`τ(χ̄₀) = μ(q)` give (6.2). No exceptional term is split off, as `W(χ,η)` here keeps it. -/
theorem rem66_expand_62 (P X : ℝ) (q : ℕ) (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P) (a : ℕ)
    (ha : Nat.Coprime a q) (η : ℝ) :
    Sp P X ((a : ℝ) / q + η) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (q.totient : ℂ) * T P X η +
        1 / (q.totient : ℂ) *
          ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * rem66_cchi χ⁻¹ 1 * Wchi P X χ η := by
  classical
  have : NeZero q := ⟨by omega⟩
  have hqf : q ≤ ⌊P⌋₊ := Nat.le_floor hqP
  rw [finsum_eq_sum_of_fintype]
  have hstep : Sp P X ((a : ℝ) / q + η) = 1 / (q.totient : ℂ) *
      ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * rem66_cchi χ⁻¹ 1 * Schi P X χ η := by
    unfold Sp Schi
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun p hp => ?_)
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have hPp : ⌊P⌋₊ < p := (mem_Ioc.mp hpI).1
    have hcop : Nat.Coprime p q := by
      rw [Nat.Prime.coprime_iff_not_dvd hpp]
      intro hd; have := Nat.le_of_dvd (by omega) hd; omega
    have he : eC (((a : ℝ) / q + η) * p) = eC (((p * a : ℕ) : ℝ) / q) * eC (η * p) := by
      rw [← rem66_eC_add]; congr 1; push_cast; ring
    rw [he, rem66_expand_61 q hq (p * a) (Nat.coprime_mul_iff_left.mpr ⟨hcop, ha⟩), mul_sum, sum_mul, mul_sum]
    refine sum_congr rfl (fun χ _ => ?_)
    push_cast
    rw [map_mul]
    ring_nf
  rw [hstep]
  have hS : ∀ χ : DirichletCharacter ℂ q,
      Schi P X χ η = Wchi P X χ η + if χ = 1 then T P X η else 0 := by
    intro χ; unfold Wchi; ring
  simp_rw [hS, mul_add, sum_add_distrib]
  have hone : ∑ χ : DirichletCharacter ℂ q,
      χ (a : ZMod q) * rem66_cchi χ⁻¹ 1 * (if χ = 1 then T P X η else 0) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) * T P X η := by
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq' univ (1 : DirichletCharacter ℂ q)]
    simp only [mem_univ, ite_true]
    have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
    rw [MulChar.one_apply hu, rem66_tau_principal q hq, one_mul]
  rw [hone]
  ring

/-- `S(α)` of P0015 display (2.2) is continuous. -/
lemma rem66_Sp_cont (P X : ℝ) : Continuous (fun α => Sp P X α) := by
  unfold Sp
  have := rem66_continuous_eC
  fun_prop

/-- `e(-(a/q + η)n) = e(-an/q) e(-ηn)`, P0015 display (6.4), page 362. -/
lemma rem66_eC_split (a q : ℕ) (n : ℕ) (η : ℝ) :
    eC (-(((a : ℝ) / q + η) * n)) = eC ((a : ℝ) * ((-(n : ℤ) : ℤ) : ℝ) / q) * eC (-(η * n)) := by
  rw [← rem66_eC_add]; congr 1; push_cast; ring

/-- `Σ'_a χ(a) e(am/q) = c_χ(m)`, the sum over `a` in P0015 display (6.4), page 362, since
`χ(a) = 0` off the reduced residues. -/
lemma rem66_coprime_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℤ) :
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        χ (a : ZMod q) * eC ((a : ℝ) * m / q) = rem66_cchi χ m := by
  unfold rem66_cchi
  refine Finset.sum_filter_of_ne (fun a _ h => ?_)
  by_contra hc
  apply h
  have : ¬ IsUnit (a : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]; exact hc
  rw [χ.map_nonunit this, zero_mul]

/-- P0015 displays (6.3) and (6.4), page 362, PROVED from (6.2): square (6.2), multiply by
`e(-nα) = e(-na/q) e(-nη)`, integrate over `|η| ≤ 1/(qQ)` and sum over reduced `a`. -/
theorem rem66_expand_64 (P X : ℝ) (q n : ℕ) (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P) :
    rem66_arcSum P X q n =
      mainWeight q n * arcIntegral P X q n + rem66_second P X q n + rem66_third P X q n := by
  classical
  have : NeZero q := ⟨by omega⟩
  set c := P / (q * X)
  set A := (range q).filter (fun a => Nat.Coprime a q)
  set μq : ℂ := ((ArithmeticFunction.moebius q : ℤ) : ℂ)
  set φq : ℂ := (q.totient : ℂ)
  set E : ℕ → ℂ := fun a => eC ((a : ℝ) * ((-(n : ℤ) : ℤ) : ℝ) / q)
  set τ : DirichletCharacter ℂ q → ℂ := fun χ => rem66_cchi χ⁻¹ 1
  have hTc := rem66_T_cont P X
  have hWc := fun χ : DirichletCharacter ℂ q => rem66_wchi_cont P X χ
  have hec := rem66_continuous_eC
  have key : ∀ a ∈ A, ∫ η in (-c)..c, Sp P X ((a : ℝ) / q + η) ^ 2 * eC (-(((a : ℝ) / q + η) * n)) =
      μq ^ 2 / φq ^ 2 * E a * (∫ η in (-c)..c, T P X η ^ 2 * eC (-(η * n))) +
      2 * μq / φq ^ 2 * ∑ χ : DirichletCharacter ℂ q, (χ (a : ZMod q) * E a) * τ χ *
        (∫ η in (-c)..c, T P X η * Wchi P X χ η * eC (-(η * n))) +
      1 / φq ^ 2 * ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
        ((χ * χ') (a : ZMod q) * E a) * τ χ * τ χ' *
          (∫ η in (-c)..c, Wchi P X χ η * Wchi P X χ' η * eC (-(η * n))) := by
    intro a ha
    have hcop : Nat.Coprime a q := (mem_filter.mp ha).2
    have hpt : ∀ η : ℝ, Sp P X ((a : ℝ) / q + η) ^ 2 * eC (-(((a : ℝ) / q + η) * n)) =
        μq ^ 2 / φq ^ 2 * E a * (T P X η ^ 2 * eC (-(η * n))) +
        2 * μq / φq ^ 2 * ∑ χ : DirichletCharacter ℂ q, (χ (a : ZMod q) * E a) * τ χ *
          (T P X η * Wchi P X χ η * eC (-(η * n))) +
        1 / φq ^ 2 * ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
          ((χ * χ') (a : ZMod q) * E a) * τ χ * τ χ' *
            (Wchi P X χ η * Wchi P X χ' η * eC (-(η * n))) := by
      intro η
      rw [rem66_expand_62 P X q hq hqP a hcop η, finsum_eq_sum_of_fintype, rem66_eC_split]
      set B := ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * rem66_cchi χ⁻¹ 1 * Wchi P X χ η
      set e := eC (-(η * n))
      have h1 : (μq / φq * T P X η + 1 / φq * B) ^ 2 * (E a * e) =
          μq ^ 2 / φq ^ 2 * E a * (T P X η ^ 2 * e) + 2 * μq / φq ^ 2 * (B * (T P X η * E a * e)) +
            1 / φq ^ 2 * (B * B * (E a * e)) := by ring
      have h2 : B * (T P X η * E a * e) = ∑ χ : DirichletCharacter ℂ q,
          (χ (a : ZMod q) * E a) * τ χ * (T P X η * Wchi P X χ η * e) := by
        rw [sum_mul]; refine sum_congr rfl (fun χ _ => by simp only [τ]; ring)
      have h3 : B * B * (E a * e) = ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
          ((χ * χ') (a : ZMod q) * E a) * τ χ * τ χ' * (Wchi P X χ η * Wchi P X χ' η * e) := by
        rw [sum_mul_sum, sum_mul]
        refine sum_congr rfl (fun χ _ => ?_)
        rw [sum_mul]
        refine sum_congr rfl (fun χ' _ => ?_)
        simp only [τ, MulChar.mul_apply]; ring
      rw [h1, h2, h3]
    have hi : ∀ f : ℝ → ℂ, Continuous f → IntervalIntegrable f MeasureTheory.volume (-c) c :=
      fun f hf => hf.intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (fun η _ => hpt η)]
    rw [intervalIntegral.integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop)),
      intervalIntegral.integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun χ _ => hi _ (by fun_prop)),
      intervalIntegral.integral_finsetSum (fun χ _ => hi _ (by fun_prop))]
    simp only [intervalIntegral.integral_const_mul]
    congr 2
    refine sum_congr rfl (fun χ _ => ?_)
    rw [intervalIntegral.integral_finsetSum (fun χ' _ => hi _ (by fun_prop))]
    simp only [intervalIntegral.integral_const_mul]
  unfold rem66_arcSum rem66_second rem66_third mainWeight arcIntegral ramanujan
  simp only [finsum_eq_sum_of_fintype]
  rw [sum_congr rfl key, sum_add_distrib, sum_add_distrib]
  congr 1
  congr 1
  · rw [← sum_mul, ← mul_sum]
    congr 2
    simp only [μq, φq]
    push_cast
    ring
  · rw [← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl (fun χ _ => ?_)
    rw [← sum_mul, ← sum_mul, rem66_coprime_sum]
  · rw [← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl (fun χ _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun χ' _ => ?_)
    rw [← sum_mul, ← sum_mul, ← sum_mul, rem66_coprime_sum]

/-! ### The arc decomposition, page 355 and (6.4) -/

/-- The major arc `𝔐(q,a) = [a/q - 1/(qQ), a/q + 1/(qQ)]` of P0015 page 355, with
`1/(qQ) = P/(qX)`. -/
def rem66_arc (P X : ℝ) (q a : ℕ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - P / (q * X)) ((a : ℝ) / q + P / (q * X))

/-- The major arcs are even mod 1, P0015 page 355: `α ∈ 𝔐` iff `α + 1 ∈ 𝔐`. -/
lemma rem66_majorArcs_add_one (P X α : ℝ) : α ∈ majorArcs P X ↔ α + 1 ∈ majorArcs P X := by
  constructor
  · rintro ⟨q, a, h1, h2, h3, h4⟩
    refine ⟨q, a + q, h1, h2, ?_, ?_⟩
    · rw [Int.gcd_comm] at h3 ⊢
      simpa [Int.gcd_comm] using h3
    · convert h4 using 2; push_cast; ring
  · rintro ⟨q, a, h1, h2, h3, h4⟩
    refine ⟨q, a - q, h1, h2, ?_, ?_⟩
    · simpa [Int.gcd_comm] using h3
    · convert h4 using 2; push_cast; ring

/-- The union `𝔐` of P0015 page 355 is measurable. -/
lemma rem66_majorArcs_meas (P X : ℝ) : MeasurableSet (majorArcs P X) := by
  have : majorArcs P X = ⋃ q : ℕ, ⋃ a : ℤ,
      {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1 ∧ |q * α - a| ≤ P / X} := by
    ext α; simp [majorArcs]
  rw [this]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
  by_cases h : 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1
  · have e : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1 ∧ |q * α - a| ≤ P / X} =
        {α : ℝ | |q * α - a| ≤ P / X} := by
      ext α; simp [h.1, h.2.1, h.2.2]
    rw [e]
    exact measurableSet_le (by fun_prop) measurable_const
  · have e : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1 ∧ |q * α - a| ≤ P / X} = ∅ := by
      ext α; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h'; exact h ⟨h'.1, h'.2.1, h'.2.2.1⟩
    rw [e]; exact MeasurableSet.empty

/-- `α ∈ 𝔐(q,a)` iff `|qα - a| ≤ P/X`, P0015 page 355. -/
lemma rem66_arc_iff (P X : ℝ) (q a : ℕ) (hq : 1 ≤ q) (α : ℝ) :
    α ∈ rem66_arc P X q a ↔ |(q : ℝ) * α - a| ≤ P / X := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have e1 : (a : ℝ) / q - P / (q * X) = ((a : ℝ) - P / X) / q := by
    rw [sub_div, div_div, mul_comm X]
  have e2 : (a : ℝ) / q + P / (q * X) = ((a : ℝ) + P / X) / q := by
    rw [add_div, div_div, mul_comm X]
  unfold rem66_arc
  rw [Set.mem_Icc, e1, e2, div_le_iff₀ hq0, le_div_iff₀ hq0, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- The index set `1 ≤ q ≤ P`, `0 ≤ a < q`, `(a,q) = 1` of the arcs of P0015 page 355. -/
noncomputable def rem66_idx (P : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 ⌊P⌋₊).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))

/-- P0015 page 355, PROVED: the major arcs are non overlapping, since for distinct reduced
fractions `|a/q - a'/q'| ≥ 1/(qq') > 1/(qQ) + 1/(q'Q)` once `8P² ≤ X`. -/
lemma rem66_arc_disjoint (P X : ℝ) (hP : 1 ≤ P) (hX : 8 * P ^ 2 ≤ X) :
    Set.Pairwise (↑(rem66_idx P))
      (Function.onFun Disjoint (fun i : (Σ _ : ℕ, ℕ) => rem66_arc P X i.1 i.2)) := by
  have hX0 : 0 < X := by nlinarith
  rintro ⟨q, a⟩ hi ⟨q', a'⟩ hj hij
  simp only [rem66_idx, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Icc, mem_filter,
    mem_range] at hi hj
  obtain ⟨⟨hq1, hqN⟩, ha, hca⟩ := hi
  obtain ⟨⟨hq1', hqN'⟩, ha', hca'⟩ := hj
  rw [Function.onFun, Set.disjoint_left]
  intro α h1 h2
  rw [rem66_arc_iff P X q a hq1] at h1
  rw [rem66_arc_iff P X q' a' hq1'] at h2
  have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hqN) (Nat.floor_le (by linarith))
  have hqP' : (q' : ℝ) ≤ P := le_trans (by exact_mod_cast hqN') (Nat.floor_le (by linarith))
  set u := P / X with hu
  have hu0 : 0 < u := by positivity
  have hPu : P * u ≤ 1 / 8 := by
    rw [hu, mul_div_assoc', div_le_iff₀ hX0]; nlinarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq0' : (0 : ℝ) ≤ q' := by positivity
  rw [abs_le] at h1 h2
  have hlt : |((a * q' : ℕ) : ℝ) - ((a' * q : ℕ) : ℝ)| < 1 := by
    push_cast
    have e : (a : ℝ) * q' - a' * q = q * (q' * α - a') - q' * (q * α - a) := by ring
    rw [e, abs_lt]
    have b1 : (q : ℝ) * (q' * α - a') ≤ q * u := mul_le_mul_of_nonneg_left h2.2 hq0
    have b2 : -(q * u) ≤ (q : ℝ) * (q' * α - a') := by nlinarith [h2.1]
    have b3 : (q' : ℝ) * (q * α - a) ≤ q' * u := mul_le_mul_of_nonneg_left h1.2 hq0'
    have b4 : -(q' * u) ≤ (q' : ℝ) * (q * α - a) := by nlinarith [h1.1]
    have b5 : (q : ℝ) * u ≤ P * u := mul_le_mul_of_nonneg_right hqP hu0.le
    have b6 : (q' : ℝ) * u ≤ P * u := mul_le_mul_of_nonneg_right hqP' hu0.le
    constructor <;> linarith
  have heq : a * q' = a' * q := by
    have hz : ((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) = 0 := by
      have : |(((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) : ℤ)| < 1 := by
        have := hlt
        exact_mod_cast this
      exact Int.abs_lt_one_iff.mp this
    omega
  have hd1 : q ∣ q' := by
    have : q ∣ q' * a := ⟨a', by rw [mul_comm q' a, heq, mul_comm]⟩
    exact (Nat.Coprime.symm hca).dvd_of_dvd_mul_right this
  have hd2 : q' ∣ q := by
    have : q' ∣ q * a' := ⟨a, by rw [mul_comm q a', ← heq, mul_comm]⟩
    exact (Nat.Coprime.symm hca').dvd_of_dvd_mul_right this
  have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
  subst hqq
  have haa : a = a' := Nat.eq_of_mul_eq_mul_right (by omega) heq
  subst haa
  exact hij rfl

/-- P0015 page 355: on the shifted unit interval `(-2P/X, 1 - 2P/X]` the set `𝔐` is exactly
the union of the arcs `𝔐(q,a)` with `0 ≤ a < q`, once `8P² ≤ X`. PROVED. -/
lemma rem66_arcs_union (P X : ℝ) (hP : 1 ≤ P) (hX : 8 * P ^ 2 ≤ X) :
    majorArcs P X ∩ Set.Ioc (-(2 * P / X)) (-(2 * P / X) + 1) =
      ⋃ i ∈ rem66_idx P, rem66_arc P X i.1 i.2 := by
  have hX0 : 0 < X := by nlinarith
  set u := P / X with hu
  have hu0 : 0 < u := by positivity
  have hPu : P * u ≤ 1 / 8 := by
    rw [hu, mul_div_assoc', div_le_iff₀ hX0]; nlinarith
  have h2u : 2 * P / X = 2 * u := by rw [hu]; ring
  rw [h2u]
  ext α
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_iUnion, rem66_idx, mem_sigma, mem_Icc,
    mem_filter, mem_range, exists_prop]
  constructor
  · rintro ⟨⟨q, a, hq1, hqP, hg, hb⟩, hlo, hhi⟩
    rw [abs_le, ← hu] at hb
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hqu : (q : ℝ) * u ≤ P * u := mul_le_mul_of_nonneg_right hqP hu0.le
    have huP : u ≤ P * u := by nlinarith
    have hm1 : (q : ℝ) * (-(2 * u)) < q * α := mul_lt_mul_of_pos_left hlo hq0
    have hm2 : (q : ℝ) * α ≤ q * (-(2 * u) + 1) := mul_le_mul_of_nonneg_left hhi hq0.le
    have hqu1 : u ≤ (q : ℝ) * u := by nlinarith
    have ha0 : (-1 : ℝ) < a := by nlinarith
    have haq : (a : ℝ) < q := by nlinarith
    have ha0' : 0 ≤ a := by
      have : (-1 : ℤ) < a := by exact_mod_cast ha0
      omega
    have haq' : a < q := by exact_mod_cast haq
    refine ⟨⟨q, a.toNat⟩, ⟨⟨hq1, Nat.le_floor hqP⟩, show a.toNat < q by omega, ?_⟩, ?_⟩
    · have : Int.gcd (a.toNat : ℤ) (q : ℤ) = 1 := by rwa [Int.toNat_of_nonneg ha0']
      rwa [Int.gcd_natCast_natCast] at this
    · rw [rem66_arc_iff P X q a.toNat hq1, abs_le]
      have : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
        rw [show ((a.toNat : ℕ) : ℝ) = ((a.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg ha0']
      rw [this, ← hu]; exact hb
  · rintro ⟨⟨q, a⟩, ⟨⟨hq1, hqN⟩, ha, hca⟩, hα⟩
    simp only at hq1 hqN ha hca hα
    rw [rem66_arc_iff P X q a hq1] at hα
    have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hqN) (Nat.floor_le (by linarith))
    have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hqu : (q : ℝ) * u ≤ P * u := mul_le_mul_of_nonneg_right hqP hu0.le
    have ha1 : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    rw [abs_le, ← hu] at hα
    have hq0' : (0 : ℝ) < q := by linarith
    refine ⟨⟨q, a, hq1, hqP, ?_, ?_⟩, ?_, ?_⟩
    · rw [Int.gcd_natCast_natCast]; exact hca
    · rw [abs_le, ← hu]; exact_mod_cast hα
    · by_contra hc
      push_neg at hc
      have : (q : ℝ) * α ≤ q * (-(2 * u)) := mul_le_mul_of_nonneg_left hc hq0'.le
      nlinarith
    · by_contra hc
      push_neg at hc
      have : (q : ℝ) * (-(2 * u) + 1) < q * α := mul_lt_mul_of_pos_left hc hq0'
      nlinarith

/-- For `δ < 1/100` and `X ≥ 64`, `1 ≤ P` and `8P² ≤ X`, with `P = X^{6δ}` of P0015 (2.4). -/
lemma rem66_P_bounds (δ X : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1 / 100) (hX : 64 ≤ X) :
    1 ≤ X ^ (6 * δ) ∧ 8 * (X ^ (6 * δ)) ^ 2 ≤ X := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  refine ⟨Real.one_le_rpow hX1 (by positivity), ?_⟩
  have h1 : X ^ (6 * δ) ≤ X ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have h2 : (X ^ (6 * δ)) ^ 2 ≤ (X ^ ((1 : ℝ) / 4)) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) h1 2
  have h3 : (X ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt X := by
    rw [← Real.rpow_mul_natCast (by linarith), Real.sqrt_eq_rpow]; norm_num
  have h4 : 8 ≤ Real.sqrt X := by
    rw [show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX
  have h5 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
  nlinarith

/-- `S(α)² e(-nα)` has period `1`, P0015 page 355: the sets are even mod 1. -/
lemma rem66_Sp_periodic (P X : ℝ) (n : ℕ) :
    Function.Periodic (fun α => Sp P X α ^ 2 * eC (-(α * n))) 1 := by
  intro α
  have hS : Sp P X (α + 1) = Sp P X α := by
    unfold Sp
    refine sum_congr rfl (fun p _ => ?_)
    rw [add_mul, one_mul, rem66_eC_add,
      show eC (p : ℝ) = 1 from by exact_mod_cast rem66_eC_int (p : ℤ), mul_one]
  have he : eC (-((α + 1) * n)) = eC (-(α * n)) := by
    rw [show -((α + 1) * n) = -(α * n) + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring, rem66_eC_add,
      rem66_eC_int, mul_one]
  simp only [hS, he]

/-- P0015 page 355 and the left side of display (6.4), page 362, PROVED. For `X ≥ 64`,
`R₁(n)` is the sum over `q ≤ P` of the arc sums: by periodicity the integral over
`𝔐 ∩ [0,1]` equals that over `𝔐 ∩ (-2P/X, 1 - 2P/X]`, which is the disjoint union of the
arcs; the arc at `0/1` cut by `[0,1]` is thereby glued. -/
theorem rem66_arc_decomp : ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ,
      R1 (X ^ (6 * δ)) X (n : ℤ) =
        ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, rem66_arcSum (X ^ (6 * δ)) X q n := by
  intro δ hδ hδ1
  refine ⟨64, fun X hX n => ?_⟩
  obtain ⟨hP1, h8⟩ := rem66_P_bounds δ X hδ hδ1 hX
  set P := X ^ (6 * δ) with hP
  have hX0 : 0 < X := by linarith
  set f : ℝ → ℂ := fun α => Sp P X α ^ 2 * eC (-(α * n)) with hf
  have hfc : Continuous f := by
    have := rem66_Sp_cont P X
    have := rem66_continuous_eC
    simp only [hf]; fun_prop
  have hM := rem66_majorArcs_meas P X
  have hper : Function.Periodic ((majorArcs P X).indicator f) 1 := by
    intro α
    by_cases h : α ∈ majorArcs P X
    · have h' := (rem66_majorArcs_add_one P X α).mp h
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem h']
      exact rem66_Sp_periodic P X n α
    · have h' : α + 1 ∉ majorArcs P X := fun h' => h ((rem66_majorArcs_add_one P X α).mpr h')
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  set c := -(2 * P / X) with hc
  have hc0 : c ≤ c + 1 := by linarith
  unfold R1
  have hR : (∫ α in majorArcs P X ∩ Set.Icc 0 1, Sp P X α ^ 2 * eC (-(α * ((n : ℤ) : ℝ)))) =
      ∫ α in majorArcs P X ∩ Set.Icc 0 1, f α := by
    simp only [hf]; push_cast; rfl
  rw [hR, Set.inter_comm, ← MeasureTheory.setIntegral_indicator hM, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hsh := hper.intervalIntegral_add_eq 0 c
  rw [zero_add] at hsh
  rw [hsh, intervalIntegral.integral_of_le hc0, MeasureTheory.setIntegral_indicator hM, Set.inter_comm,
    hc, rem66_arcs_union P X hP1 h8,
    MeasureTheory.integral_biUnion_finset (s := fun i : (Σ _ : ℕ, ℕ) => rem66_arc P X i.1 i.2) _
      (fun i _ => by unfold rem66_arc; exact measurableSet_Icc)
      (rem66_arc_disjoint P X hP1 h8) (fun i _ => by unfold rem66_arc; exact hfc.integrableOn_Icc)]
  rw [rem66_idx, sum_sigma]
  refine sum_congr rfl (fun q hq => ?_)
  unfold rem66_arcSum
  refine sum_congr rfl (fun a _ => ?_)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
  have hε : 0 ≤ P / (q * X) := by positivity
  rw [rem66_arc, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hcomp := intervalIntegral.integral_comp_add_left f ((a : ℝ) / q)
    (a := -(P / (q * X))) (b := P / (q * X))
  simp only [hf] at hcomp ⊢
  rw [hcomp, ← sub_eq_add_neg]

/-! ### Display (6.8) -/

open DirichletCharacter in
/-- P0015 page 362, before (6.8), grouping the characters mod `q` by the primitive character
inducing them, PROVED. Each `χ` mod `q` is induced by exactly one primitive `χ*` mod `r` with
`r ∣ q`, namely `r` its conductor and `χ*` its primitive character, and every primitive `ψ` mod
`r ∣ q` induces one `χ`. -/
theorem rem66_group_by_primitive {q : ℕ} (hq : 1 ≤ q) (F : DirichletCharacter ℂ q → ℝ)
    (H : (r : ℕ) → DirichletCharacter ℂ r → ℝ) :
    ∑ᶠ χ : DirichletCharacter ℂ q, F χ * H χ.conductor χ.primitiveCharacter =
      ∑ r ∈ Icc 1 q, if h : r ∣ q then
        ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, F (changeLevel h ψ.1) * H r ψ.1
      else 0 := by
  classical
  have : NeZero q := ⟨by omega⟩
  rw [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := Icc 1 q)
    (g := fun χ : DirichletCharacter ℂ q => χ.conductor)]
  swap
  · intro χ _
    rw [mem_Icc]
    exact ⟨Nat.pos_of_ne_zero χ.conductor_ne_zero,
      Nat.le_of_dvd (by omega) χ.conductor_dvd_level⟩
  refine sum_congr rfl (fun r _ => ?_)
  by_cases h : r ∣ q
  · rw [dif_pos h, finsum_eq_sum_of_fintype]
    symm
    refine Finset.sum_bij (fun ψ _ => changeLevel h ψ.1) ?_ ?_ ?_ ?_
    · intro ψ _
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [conductor_changeLevel]
      exact ψ.2
    · intro ψ₁ _ ψ₂ _ he
      exact Subtype.ext (changeLevel_injective h he)
    · intro χ hχ
      have hc : χ.conductor = r := (mem_filter.mp hχ).2
      have key : ∀ (c : ℕ) (φ : DirichletCharacter ℂ c) (hcq : c ∣ q), c = r → φ.IsPrimitive →
          changeLevel hcq φ = χ →
          ∃ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, changeLevel h ψ.1 = χ := by
        rintro c φ hcq rfl hp he
        exact ⟨⟨φ, hp⟩, he⟩
      obtain ⟨ψ, hψ⟩ := key χ.conductor χ.primitiveCharacter χ.conductor_dvd_level hc
        χ.primitiveCharacter_isPrimitive χ.changeLevel_primitiveCharacter
      exact ⟨ψ, mem_univ _, hψ⟩
    · intro ψ _
      congr 1
      have key : ∀ (c : ℕ) (φ : DirichletCharacter ℂ c) (hcq : c ∣ q), c = r →
          changeLevel hcq φ = changeLevel h ψ.1 →
          (⟨c, φ⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨r, ψ.1⟩ := by
        rintro c φ hcq rfl he
        rw [changeLevel_injective h he]
      have hs := key (changeLevel h ψ.1).conductor (changeLevel h ψ.1).primitiveCharacter
        (changeLevel h ψ.1).conductor_dvd_level
        (by rw [conductor_changeLevel]; exact ψ.2)
        (changeLevel h ψ.1).changeLevel_primitiveCharacter
      exact (congrArg (fun s : Σ r : ℕ, DirichletCharacter ℂ r => H s.1 s.2) hs).symm
  · rw [dif_neg h]
    refine sum_eq_zero (fun χ hχ => ?_)
    exfalso
    have hc : χ.conductor = r := (mem_filter.mp hχ).2
    exact h (hc ▸ χ.conductor_dvd_level)

open DirichletCharacter in
/-- LEAF: P0015 Lemma 5.5, display (5.4), page 360, class HARD. For primitive `χ₁` mod `r₁`
and `χ₂` mod `r₂` and `m ≠ 0`, the sum over `q` divisible by `r₁` and `r₂` of
`φ(q)⁻² |c_{χ₁χ₂χ₀}(m) τ(χ̄₁χ₀) τ(χ̄₂χ₀)|` is `≪ |m|/φ(|m|)`, here truncated to `q ≤ N`, the
induced characters written as `changeLevel`. The implied constant is absolute. -/
theorem rem66_lemma55 : ∃ C : ℝ, 0 < C ∧ ∀ (r₁ r₂ : ℕ) (ψ₁ : DirichletCharacter ℂ r₁)
    (ψ₂ : DirichletCharacter ℂ r₂), ψ₁.IsPrimitive → ψ₂.IsPrimitive → ∀ m : ℤ, m ≠ 0 →
    ∀ N : ℕ, ∑ q ∈ Icc 1 N, (if h : r₁ ∣ q ∧ r₂ ∣ q then
        ‖rem66_cchi (changeLevel h.1 ψ₁ * changeLevel h.2 ψ₂) m *
          rem66_cchi (changeLevel h.1 ψ₁)⁻¹ 1 * rem66_cchi (changeLevel h.2 ψ₂)⁻¹ 1‖ /
          (q.totient : ℝ) ^ 2
      else 0) ≤ C * ((m.natAbs : ℝ) / (m.natAbs.totient : ℝ)) := by
  sorry

open DirichletCharacter in
/-- P0015 display (6.8), page 362, the first sum, PROVED from the grouping lemma, Lemma 5.5 with
`χ₂` the character mod `1`, and Lemma 5.2 `τ(χ̄₀) = μ(q)`:
`Σ_{q≤P} μ(q)²φ(q)⁻² Σ_χ |c_χ(-n) τ(χ̄)| W(χ*) ≪ n φ(n)⁻¹ W`. -/
theorem rem66_group_second_of (hL : type_of% @rem66_lemma55) : ∃ C : ℝ, 0 < C ∧ ∀ P X : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∑ q ∈ Icc 1 ⌊P⌋₊, rem66_A2 P X q n ≤ C * ((n : ℝ) / (n.totient : ℝ)) * mvW P X := by
  classical
  obtain ⟨C, hC, h55⟩ := hL
  refine ⟨C, hC, fun P X n hn => ?_⟩
  set N := ⌊P⌋₊
  set ρ := (n : ℝ) / (n.totient : ℝ)
  set F : (q : ℕ) → DirichletCharacter ℂ q → ℝ := fun q χ =>
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      ‖rem66_cchi χ (-(n : ℤ)) * rem66_cchi χ⁻¹ 1‖ with hF
  set D : ℕ → ℕ → ℝ := fun q r => if h : r ∣ q then
      ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
        F q (changeLevel h ψ.1) * Wnorm P X ψ.1 else 0 with hD
  have step1 : ∀ q ∈ Icc 1 N, rem66_A2 P X q n = ∑ r ∈ Icc 1 N, D q r := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqN : q ≤ N := (mem_Icc.mp hq).2
    have e1 : rem66_A2 P X q n = ∑ᶠ χ : DirichletCharacter ℂ q,
        F q χ * (fun r (ψ : DirichletCharacter ℂ r) => Wnorm P X ψ) χ.conductor
          χ.primitiveCharacter := by
      unfold rem66_A2
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, mul_sum]
      refine sum_congr rfl (fun χ _ => ?_)
      simp only [hF]; ring
    rw [e1, rem66_group_by_primitive hq1 (F q) (fun r ψ => Wnorm P X ψ)]
    refine sum_subset (Icc_subset_Icc le_rfl hqN) (fun r hrN hrq => ?_)
    have : ¬ r ∣ q := by
      intro h; apply hrq; rw [mem_Icc] at hrN ⊢
      exact ⟨hrN.1, Nat.le_of_dvd (by omega) h⟩
    simp only [dif_neg this]
  rw [sum_congr rfl step1, sum_comm]
  unfold mvW
  rw [mul_sum]
  refine sum_le_sum (fun r hr => ?_)
  have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
  have hW : ∀ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, 0 ≤ Wnorm P X ψ.1 :=
    fun ψ => Real.sqrt_nonneg _
  have e2 : ∑ q ∈ Icc 1 N, D q r = ∑ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
      (∑ q ∈ Icc 1 N, if h : r ∣ q then F q (changeLevel h ψ.1) else 0) * Wnorm P X ψ.1 := by
    simp only [hD, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl (fun q _ => ?_)
    by_cases h : r ∣ q
    · simp only [dif_pos h, finsum_eq_sum_of_fintype]
    · simp only [dif_neg h, zero_mul, sum_const_zero]
  rw [e2, finsum_eq_sum_of_fintype, mul_sum]
  refine sum_le_sum (fun ψ _ => ?_)
  refine mul_le_mul_of_nonneg_right ?_ (hW ψ)
  have h1 := h55 r 1 ψ.1 1 ψ.2 isPrimitive_one_level_one (-(n : ℤ)) (by omega) N
  have hnat : (-(n : ℤ)).natAbs = n := by simp
  rw [hnat] at h1
  refine le_trans (le_of_eq (sum_congr rfl (fun q hq => ?_))) h1
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  by_cases h : r ∣ q
  · rw [dif_pos h, dif_pos ⟨h, one_dvd q⟩]
    have ht : rem66_cchi (1 : DirichletCharacter ℂ q) 1 =
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
      have := rem66_tau_principal q hq1; rwa [inv_one] at this
    simp only [hF, changeLevel_one, mul_one, inv_one, ht]
    rw [norm_mul _ (((ArithmeticFunction.moebius q : ℤ) : ℂ)), Complex.norm_intCast]
    have habs : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| =
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 := by
      rw [← Int.cast_abs, ← Int.cast_pow, ArithmeticFunction.abs_moebius,
        ArithmeticFunction.moebius_sq]
    rw [habs]; ring
  · rw [dif_neg h, dif_neg (fun h' => h h'.1)]

open Classical DirichletCharacter in
/-- The grouping of P0015 page 362 before (6.8) with finite sums and the range of `r` widened
to `1 ≤ r ≤ N` for `q ≤ N`. -/
lemma rem66_group_sum {q : ℕ} (hq : 1 ≤ q) (N : ℕ) (hqN : q ≤ N)
    (F : DirichletCharacter ℂ q → ℝ) (H : (r : ℕ) → DirichletCharacter ℂ r → ℝ) :
    ∑ χ : DirichletCharacter ℂ q, F χ * H χ.conductor χ.primitiveCharacter =
      ∑ r ∈ Icc 1 N, if h : r ∣ q then
        ∑ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, F (changeLevel h ψ.1) * H r ψ.1
      else 0 := by
  classical
  rw [← finsum_eq_sum_of_fintype, rem66_group_by_primitive hq F H]
  refine sum_subset (Icc_subset_Icc le_rfl hqN) (fun r hrN hrq => ?_) |>.trans ?_
  · have : ¬ r ∣ q := by
      intro h; apply hrq; rw [mem_Icc] at hrN ⊢
      exact ⟨hrN.1, Nat.le_of_dvd (by omega) h⟩
    simp only [dif_neg this]
  · refine sum_congr rfl (fun r _ => ?_)
    by_cases h : r ∣ q
    · simp only [dif_pos h, finsum_eq_sum_of_fintype]
    · simp only [dif_neg h]

open DirichletCharacter in
/-- P0015 display (6.8), page 362, the second sum, PROVED from the grouping lemma twice and
Lemma 5.5: `Σ_{q≤P} φ(q)⁻² Σ_{χ,χ'} |c_{χχ'}(-n) τ(χ̄) τ(χ̄')| W(χ*) W(χ'*) ≪ n φ(n)⁻¹ W²`. -/
theorem rem66_group_third_of (hL : type_of% @rem66_lemma55) : ∃ C : ℝ, 0 < C ∧ ∀ P X : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∑ q ∈ Icc 1 ⌊P⌋₊, rem66_A3 P X q n ≤ C * ((n : ℝ) / (n.totient : ℝ)) * mvW P X ^ 2 := by
  classical
  obtain ⟨C, hC, h55⟩ := hL
  refine ⟨C, hC, fun P X n hn => ?_⟩
  set N := ⌊P⌋₊
  set ρ := (n : ℝ) / (n.totient : ℝ)
  set G : (q : ℕ) → DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℝ := fun q χ χ' =>
    ‖rem66_cchi (χ * χ') (-(n : ℤ)) * rem66_cchi χ⁻¹ 1 * rem66_cchi χ'⁻¹ 1‖ /
      (q.totient : ℝ) ^ 2 with hG
  set Wf : (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun r ψ => Wnorm P X ψ with hWf
  set E : ℕ → ℕ → ℕ → ℝ := fun q r₁ r₂ => if h : r₁ ∣ q ∧ r₂ ∣ q then
      ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
        ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
          G q (changeLevel h.1 ψ₁.1) (changeLevel h.2 ψ₂.1) * Wnorm P X ψ₁.1 * Wnorm P X ψ₂.1
      else 0 with hE
  have step1 : ∀ q ∈ Icc 1 N, rem66_A3 P X q n = ∑ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, E q r₁ r₂ := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqN : q ≤ N := (mem_Icc.mp hq).2
    have e1 : rem66_A3 P X q n = ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
        (G q χ χ' * Wf χ.conductor χ.primitiveCharacter) *
          Wf χ'.conductor χ'.primitiveCharacter := by
      unfold rem66_A3
      simp only [finsum_eq_sum_of_fintype, mul_sum]
      refine sum_congr rfl (fun χ _ => sum_congr rfl (fun χ' _ => ?_))
      simp only [hG, hWf]; ring
    rw [e1]
    simp_rw [rem66_group_sum hq1 N hqN _ Wf]
    rw [sum_comm]
    have e2 : ∀ r₂ ∈ Icc 1 N, (∑ χ : DirichletCharacter ℂ q, if h : r₂ ∣ q then
        ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
          G q χ (changeLevel h ψ₂.1) * Wf χ.conductor χ.primitiveCharacter * Wf r₂ ψ₂.1
        else 0) = ∑ r₁ ∈ Icc 1 N, E q r₁ r₂ := by
      intro r₂ _
      by_cases h2 : r₂ ∣ q
      · simp only [dif_pos h2]
        have e3 : ∀ χ : DirichletCharacter ℂ q, ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
            G q χ (changeLevel h2 ψ₂.1) * Wf χ.conductor χ.primitiveCharacter * Wf r₂ ψ₂.1 =
            (∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
              G q χ (changeLevel h2 ψ₂.1) * Wf r₂ ψ₂.1) * Wf χ.conductor χ.primitiveCharacter := by
          intro χ; rw [sum_mul]; refine sum_congr rfl (fun ψ₂ _ => by ring)
        simp_rw [e3]
        rw [rem66_group_sum hq1 N hqN _ Wf]
        refine sum_congr rfl (fun r₁ _ => ?_)
        by_cases h1 : r₁ ∣ q
        · simp only [hE, dif_pos h1, dif_pos (And.intro h1 h2), sum_mul]
          refine sum_congr rfl (fun ψ₁ _ => sum_congr rfl (fun ψ₂ _ => ?_))
          simp only [hWf]; ring
        · simp only [hE, dif_neg h1]
          rw [dif_neg (fun h => h1 h.1)]
      · simp only [dif_neg h2, sum_const_zero]
        refine (sum_eq_zero (fun r₁ _ => ?_)).symm
        simp only [hE]; rw [dif_neg (fun h => h2 h.2)]
    rw [sum_congr rfl e2, sum_comm]
  rw [sum_congr rfl step1, sum_comm]
  rw [sum_congr rfl (fun r₁ _ => sum_comm)]
  -- now Σ_{r₁} Σ_{r₂} Σ_q E q r₁ r₂
  set w : ℕ → ℝ := fun r => ∑ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, Wnorm P X ψ.1
    with hw
  have hmv : mvW P X = ∑ r ∈ Icc 1 N, w r := by
    unfold mvW; refine sum_congr rfl (fun r _ => ?_); rw [finsum_eq_sum_of_fintype]
  have hbound : ∀ r₁ ∈ Icc 1 N, ∀ r₂ ∈ Icc 1 N, ∑ q ∈ Icc 1 N, E q r₁ r₂ ≤ C * ρ * (w r₁ * w r₂) := by
    intro r₁ _ r₂ _
    set K : ℕ → {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive} →
        {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive} → ℝ := fun q ψ₁ ψ₂ =>
      if h : r₁ ∣ q ∧ r₂ ∣ q then G q (changeLevel h.1 ψ₁.1) (changeLevel h.2 ψ₂.1) else 0
      with hK
    have eq1 : ∑ q ∈ Icc 1 N, E q r₁ r₂ =
        ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
          ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
            (∑ q ∈ Icc 1 N, K q ψ₁ ψ₂) * (Wnorm P X ψ₁.1 * Wnorm P X ψ₂.1) := by
      calc ∑ q ∈ Icc 1 N, E q r₁ r₂
          = ∑ q ∈ Icc 1 N, ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
              ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
                K q ψ₁ ψ₂ * (Wnorm P X ψ₁.1 * Wnorm P X ψ₂.1) := by
            refine sum_congr rfl (fun q _ => ?_)
            by_cases h : r₁ ∣ q ∧ r₂ ∣ q
            · simp only [hE, hK, dif_pos h]
              refine sum_congr rfl (fun ψ₁ _ => sum_congr rfl (fun ψ₂ _ => by ring))
            · simp only [hE, hK, dif_neg h, zero_mul, sum_const_zero]
        _ = ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive}, ∑ q ∈ Icc 1 N,
              ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
                K q ψ₁ ψ₂ * (Wnorm P X ψ₁.1 * Wnorm P X ψ₂.1) := sum_comm
        _ = ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
              ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive}, ∑ q ∈ Icc 1 N,
                K q ψ₁ ψ₂ * (Wnorm P X ψ₁.1 * Wnorm P X ψ₂.1) :=
            sum_congr rfl (fun ψ₁ _ => sum_comm)
        _ = _ := by simp only [sum_mul]
    rw [eq1]
    have hw1 : w r₁ * w r₂ = ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
        ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
          Wnorm P X ψ₁.1 * Wnorm P X ψ₂.1 := by
      simp only [hw]; rw [sum_mul_sum]
    rw [hw1, mul_sum]
    refine sum_le_sum (fun ψ₁ _ => ?_)
    rw [mul_sum]
    refine sum_le_sum (fun ψ₂ _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h1 := h55 r₁ r₂ ψ₁.1 ψ₂.1 ψ₁.2 ψ₂.2 (-(n : ℤ)) (by omega) N
    have hnat : (-(n : ℤ)).natAbs = n := by simp
    rw [hnat] at h1
    exact h1
  have hw0 : ∀ r, 0 ≤ w r := fun r => sum_nonneg (fun ψ _ => Real.sqrt_nonneg _)
  calc ∑ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, ∑ q ∈ Icc 1 N, E q r₁ r₂
      ≤ ∑ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, C * ρ * (w r₁ * w r₂) :=
        sum_le_sum (fun r₁ h1 => sum_le_sum (fun r₂ h2 => hbound r₁ h1 r₂ h2))
    _ = C * ρ * mvW P X ^ 2 := by
        rw [hmv, sq, sum_mul_sum, mul_sum]
        refine sum_congr rfl (fun r₁ _ => ?_)
        rw [mul_sum]

/-! ### Assembly -/

/-- `A₂ ≥ 0`, the first sum of P0015 display (6.6) has nonnegative terms. -/
lemma rem66_A2_nonneg (P X : ℝ) (q n : ℕ) : 0 ≤ rem66_A2 P X q n := by
  unfold rem66_A2
  refine mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (finsum_nonneg (fun χ => ?_))
  exact mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- For `δ < 1/100` and `X ≥ 4`, `2P ≤ X` with `P = X^{6δ}`, the range where P0015 display (6.7)
applies. -/
lemma rem66_two_P_le (δ X : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1 / 100) (hX : 4 ≤ X) :
    2 * X ^ (6 * δ) ≤ X := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have h1 : X ^ (6 * δ) ≤ X ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have h2 : X ^ ((1 : ℝ) / 2) = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  have h3 : 2 ≤ Real.sqrt X := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX
  have h4 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
  rw [h2] at h1
  nlinarith

/-- P0015 displays (6.1) to (6.9), pages 361 to 363, the statement of `mv_remainder_66_68`,
PROVED sorry free CONDITIONAL ON Lemma 5.5 of page 360, passed as the hypothesis `hL`. -/
theorem rem66_of_lemma55 (hL : type_of% @rem66_lemma55) : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      ‖R1 (X ^ (6 * δ)) X (n : ℤ) -
          ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, mainWeight q n * arcIntegral (X ^ (6 * δ)) X q n‖ ≤
        C * ((n : ℝ) / (n.totient : ℝ)) *
          (mvW (X ^ (6 * δ)) X * Real.sqrt X + mvW (X ^ (6 * δ)) X ^ 2) := by
  obtain ⟨C2, hC2, h2⟩ := rem66_group_second_of hL
  obtain ⟨C3, hC3, h3⟩ := rem66_group_third_of hL
  refine ⟨2 * C2 + C3, by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨X₁, hX₁⟩ := rem66_arc_decomp δ hδ hδ1
  refine ⟨max X₁ 4, ?_⟩
  intro X hX n hn hnX
  have hXa : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  set P := X ^ (6 * δ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hX0.le _
  have hPX : 2 * P ≤ X := rem66_two_P_le δ X hδ hδ1 hX4
  set s := Icc 1 ⌊P⌋₊ with hs
  have hqs : ∀ q ∈ s, 1 ≤ q ∧ (q : ℝ) ≤ P := fun q hq =>
    ⟨(mem_Icc.mp hq).1, le_trans (by exact_mod_cast (mem_Icc.mp hq).2) (Nat.floor_le hP0)⟩
  have hdiff : R1 P X (n : ℤ) - ∑ q ∈ s, mainWeight q n * arcIntegral P X q n =
      ∑ q ∈ s, (rem66_second P X q n + rem66_third P X q n) := by
    rw [hX₁ X hXa n, ← sum_sub_distrib]
    refine sum_congr rfl (fun q hq => ?_)
    rw [rem66_expand_64 P X q n (hqs q hq).1 (hqs q hq).2]
    ring
  rw [hdiff]
  set W := mvW P X
  set ρ := (n : ℝ) / (n.totient : ℝ)
  have hρ0 : 0 ≤ ρ := by positivity
  have hW0 : 0 ≤ W := sum_nonneg (fun r _ => finsum_nonneg (fun χ => Real.sqrt_nonneg _))
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hterm : ∀ q ∈ s, ‖rem66_second P X q n + rem66_third P X q n‖ ≤
      2 * Real.sqrt X * rem66_A2 P X q n + rem66_A3 P X q n := by
    intro q hq
    obtain ⟨hq1, hqP⟩ := hqs q hq
    have hT := rem66_T_L2 P X q hq1 hP0 hX0 hPX
    have hsT := Real.sqrt_le_sqrt hT
    have hA := rem66_A2_nonneg P X q n
    calc ‖rem66_second P X q n + rem66_third P X q n‖
        ≤ ‖rem66_second P X q n‖ + ‖rem66_third P X q n‖ := norm_add_le _ _
      _ ≤ 2 * Real.sqrt (∫ η in (-(P / (q * X)))..(P / (q * X)), ‖T P X η‖ ^ 2) *
            rem66_A2 P X q n + rem66_A3 P X q n :=
          add_le_add (rem66_cs_second P X q n hq1 hqP hX0) (rem66_cs_third P X q n hq1 hqP hX0)
      _ ≤ 2 * Real.sqrt X * rem66_A2 P X q n + rem66_A3 P X q n := by
          gcongr
  calc ‖∑ q ∈ s, (rem66_second P X q n + rem66_third P X q n)‖
      ≤ ∑ q ∈ s, ‖rem66_second P X q n + rem66_third P X q n‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ s, (2 * Real.sqrt X * rem66_A2 P X q n + rem66_A3 P X q n) := sum_le_sum hterm
    _ = 2 * Real.sqrt X * ∑ q ∈ s, rem66_A2 P X q n + ∑ q ∈ s, rem66_A3 P X q n := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ 2 * Real.sqrt X * (C2 * ρ * W) + C3 * ρ * W ^ 2 := by
        gcongr
        · exact h2 P X n hn
        · exact h3 P X n hn
    _ ≤ (2 * C2 + C3) * ρ * (W * Real.sqrt X + W ^ 2) := by
        have h1 : 0 ≤ C3 * ρ * (W * Real.sqrt X) := by positivity
        have h2' : 0 ≤ 2 * C2 * ρ * W ^ 2 := by positivity
        nlinarith

/-- P0015 displays (6.1) to (6.9), pages 361 to 363: the exact statement of
`mv_remainder_66_68`. PROVED from the leaves above; the only leaf left is `rem66_lemma55`. -/
theorem rem66_of_leaves : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      ‖R1 (X ^ (6 * δ)) X (n : ℤ) -
          ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, mainWeight q n * arcIntegral (X ^ (6 * δ)) X q n‖ ≤
        C * ((n : ℝ) / (n.totient : ℝ)) *
          (mvW (X ^ (6 * δ)) X * Real.sqrt X + mvW (X ^ (6 * δ)) X ^ 2) :=
  rem66_of_lemma55 rem66_lemma55

/-- Check that `rem66_of_leaves` has exactly the type of `mv_remainder_66_68`. -/
example : True :=
  let _f : type_of% @mv_remainder_66_68 := rem66_of_leaves
  trivial

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_arc_decomp
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_expand_64
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_of_lemma55
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_of_leaves

