/-
P0069 pages 18, 19 and 24: the leaf `leaf_339_lemma4_variant` of SPLIT_lemma10_small_L_339 is
refuted as stated. The leaf drops the height condition T/2 <= abs t <= T for principal points,
which the parent `lemma10_small_L_339_split` has. A single principal point at t = 0 with
M = N = x^0.45, L = x^0.1, q = 1, T = x^0.4 meets every hypothesis of the leaf, the fourth
moment one included, yet ||MNL||_1 >= x^(1/2) / 27. The parent statement is not refuted.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_339

namespace LeanLab.BakerHarmanPintz1997
open Finset Filter
open scoped Real

/-- Proved helper: the trivial character mod 1 is 1 everywhere. -/
theorem p4_chi_one (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

/-- Proved helper: the value at 1/2 of an interval polynomial with the trivial character
mod 1 has norm the real sum of n^(-1/2). -/
theorem p4_eval_norm (a b F : ℝ) :
    ‖(longDP a b F).eval (1 : DirichletCharacter ℂ 1) (half 0)‖ =
      ∑ n ∈ Finset.Ioo ⌊a * F⌋₊ ⌈b * F⌉₊, 1 / √(n : ℝ) := by
  have hh : half 0 = ((1 / 2 : ℝ) : ℂ) := by simp [half]
  have hterm : ∀ n : ℕ, (n : ℂ) ^ (-(half 0)) = ((1 / √(n : ℝ) : ℝ) : ℂ) := by
    intro n
    rw [hh, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]
  unfold DP.eval longDP
  simp only [p4_chi_one, one_mul, hterm]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg]
  exact sum_nonneg fun n _ => by positivity

/-- Proved helper: the interval polynomial with c1 = 1/4, c2 = 4 has length F. -/
theorem p4_hasLen (F : ℝ) : (longDP (1 / 4) 4 F).HasLen F (1 / 4) 4 := by
  intro n hn
  simp only [longDP, Finset.mem_Ioo] at hn
  constructor
  · have h := Nat.lt_floor_add_one ((1 / 4 : ℝ) * F)
    have h2 : (⌊(1 / 4 : ℝ) * F⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
    linarith
  · exact (Nat.lt_ceil).1 hn.2

/-- Proved helper: coefficients 1 satisfy (3.1) with B = 0. -/
theorem p4_coef (F : ℝ) : (longDP (1 / 4) 4 F).Coef31 0 := by
  intro n _
  simp [longDP, Real.rpow_zero]

/-- Proved helper: lower bound, for F >= 1 the sum of n^(-1/2) over the interval is at least
sqrt F / 3. -/
theorem p4_lower (F : ℝ) (hF : 1 ≤ F) :
    √F / 3 ≤ ∑ n ∈ Finset.Ioo ⌊(1 / 4 : ℝ) * F⌋₊ ⌈4 * F⌉₊, 1 / √(n : ℝ) := by
  set I := Finset.Ioo ⌊(1 / 4 : ℝ) * F⌋₊ ⌈4 * F⌉₊
  have hterm : ∀ n ∈ I, 1 / √(5 * F) ≤ 1 / √(n : ℝ) := by
    intro n hn
    simp only [I, Finset.mem_Ioo] at hn
    have h1 : (n : ℝ) < 4 * F := (Nat.lt_ceil).1 hn.2
    have h0 : (0 : ℝ) < n := by
      have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
      exact_mod_cast this
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 h0)
    exact Real.sqrt_le_sqrt (by linarith)
  have hcard : F ≤ (I.card : ℝ) := by
    simp only [I, Nat.card_Ioo]
    have hc := Nat.le_ceil (4 * F)
    have hf := Nat.floor_le (show 0 ≤ (1 / 4 : ℝ) * F by linarith)
    have hlt : ⌊(1 / 4 : ℝ) * F⌋₊ + 1 ≤ ⌈4 * F⌉₊ := by
      have : (⌊(1 / 4 : ℝ) * F⌋₊ : ℝ) + 1 < ⌈4 * F⌉₊ := by linarith
      exact_mod_cast this.le
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hsum : (I.card : ℝ) * (1 / √(5 * F)) ≤ ∑ n ∈ I, 1 / √(n : ℝ) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hterm
  have hF0 : 0 < F := by linarith
  have h5 : √(5 * F) = √5 * √F := Real.sqrt_mul (by norm_num) F
  have hsF : 0 < √F := Real.sqrt_pos.2 hF0
  have hs5 : √5 ≤ 3 := by
    rw [show (3 : ℝ) = √(3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs50 : 0 < √5 := by positivity
  have key : √F / 3 ≤ F * (1 / √(5 * F)) := by
    calc √F / 3 ≤ √F / √5 := div_le_div_of_nonneg_left hsF.le hs50 hs5
      _ = √F * √F / (√5 * √F) := (mul_div_mul_right _ _ hsF.ne').symm
      _ = F * (1 / √(5 * F)) := by rw [Real.mul_self_sqrt hF0.le, h5, mul_one_div]
  have hnn : 0 ≤ 1 / √(5 * F) := by positivity
  linarith [mul_le_mul_of_nonneg_right hcard hnn]

/-- Proved helper: upper bound, every term is at most 1, so the sum is at most 4F + 1. -/
theorem p4_upper (F : ℝ) (hF : 0 ≤ F) :
    ∑ n ∈ Finset.Ioo ⌊(1 / 4 : ℝ) * F⌋₊ ⌈4 * F⌉₊, 1 / √(n : ℝ) ≤ 4 * F + 1 := by
  set I := Finset.Ioo ⌊(1 / 4 : ℝ) * F⌋₊ ⌈4 * F⌉₊
  have hterm : ∀ n ∈ I, 1 / √(n : ℝ) ≤ 1 := by
    intro n hn
    simp only [I, Finset.mem_Ioo] at hn
    have h1 : (1 : ℝ) ≤ n := by
      have : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le _) hn.1
      exact_mod_cast this
    rw [div_le_one (Real.sqrt_pos.2 (by linarith))]
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt h1
  have hs : ∑ n ∈ I, 1 / √(n : ℝ) ≤ I.card • (1 : ℝ) := Finset.sum_le_card_nsmul _ _ _ hterm
  have hcard : (I.card : ℝ) ≤ 4 * F + 1 := by
    simp only [I, Nat.card_Ioo]
    have hc := (Nat.ceil_lt_add_one (show 0 ≤ 4 * F by linarith)).le
    have : (⌈4 * F⌉₊ - ⌊(1 / 4 : ℝ) * F⌋₊ - 1 : ℕ) ≤ ⌈4 * F⌉₊ := by omega
    have h2 : ((⌈4 * F⌉₊ - ⌊(1 / 4 : ℝ) * F⌋₊ - 1 : ℕ) : ℝ) ≤ ⌈4 * F⌉₊ := by exact_mod_cast this
    linarith
  rw [nsmul_eq_mul, mul_one] at hs
  linarith

/-- The configuration of the counterexample: q = 1, T = x^0.4, one principal point at t = 0. -/
noncomputable def p4Cfg (x : ℝ) : Cfg := ⟨1, x ^ (0.4 : ℝ), {((0 : ℝ), (1 : DirichletCharacter ℂ 1))}⟩

/-- FALSE, Lean checked: the leaf `leaf_339_lemma4_variant` of SPLIT_lemma10_small_L_339, restated
verbatim, fails. Its hypotheses omit the principal height condition of the parent. -/
theorem leaf_339_lemma4_variant_false : ¬ (
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2)) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    (∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ))) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮) := by
  rintro ⟨ε0, hε0, h⟩
  set ε := min (ε0 / 2) (1 / 10) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεlt : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε10 : ε ≤ 1 / 10 := min_le_right _ _
  let Ml : ℝ → ℝ := fun x => |x| ^ (0.45 : ℝ)
  let Ll : ℝ → ℝ := fun x => |x| ^ (0.1 : ℝ)
  let Nl : ℝ → ℝ := fun x => x / (Ml x * Ll x)
  let 𝒮 : ℝ → Set Cfg := fun x => {c | c = p4Cfg x ∧ c.Std x}
  have hpos : ∀ x : ℝ, 0 < x → Nl x = x ^ (0.45 : ℝ) := by
    intro x hx
    simp only [Nl, Ml, Ll, abs_of_pos hx]
    rw [← Real.rpow_add hx, div_eq_iff (Real.rpow_pos_of_pos hx _).ne', ← Real.rpow_add hx]
    conv_lhs => rw [← Real.rpow_one x]
    norm_num
  have hprod : ∀ x, Ml x * Nl x * Ll x = x := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Nl]
    · have h1 : Ml x * Ll x ≠ 0 := by
        have := abs_pos.2 hx
        simp only [Ml, Ll]; positivity
      simp only [Nl]
      have e : Ml x * (x / (Ml x * Ll x)) * Ll x = x * ((Ml x * Ll x) / (Ml x * Ll x)) := by ring
      rw [e, div_self h1, mul_one]
  have hfam : FamOK (fun x => [longDP (1 / 4) 4 (Ml x), longDP (1 / 4) 4 (Nl x)]) [Ml, Nl] 0
      (1 / 4) 4 := by
    intro x
    refine ⟨rfl, ?_⟩
    intro i hi hi'
    have hi0 : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi0 with rfl | rfl
    · exact ⟨p4_hasLen _, p4_coef _⟩
    · exact ⟨p4_hasLen _, p4_coef _⟩
  have hmem : ∀ x, ∀ c ∈ 𝒮 x, c = p4Cfg x ∧ c.Std x := fun x c hc => hc
  have hx1 : ∀ x, ∀ c ∈ 𝒮 x, 1 ≤ x := by
    intro x c hc
    obtain ⟨rfl, hs⟩ := hmem x c hc
    have := hs.2.2.1
    simpa [p4Cfg] using this
  have hcfg := h ε hε hεlt 0 (1 / 4) 4 (fun x => longDP (1 / 4) 4 (Ml x))
    (fun x => longDP (1 / 4) 4 (Nl x)) Ml Nl Ll 𝒮 (by norm_num) (by norm_num) hfam hprod
    (fun x c hc => (hmem x c hc).2)
    ⟨0, fun x _ c hc => by
      have hx := hx1 x c hc
      obtain ⟨rfl, -⟩ := hmem x c hc
      simp only [p4Cfg, Nat.cast_one, one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)⟩
    (fun x c hc => by
      have hx := hx1 x c hc
      have hx0 : 0 < x := by linarith
      rw [hpos x hx0]
      simp only [Ml, abs_of_pos hx0, max_self]
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith))
    (fun x c hc => by
      have hx := hx1 x c hc
      obtain ⟨rfl, -⟩ := hmem x c hc
      simp only [Ll, p4Cfg, Nat.cast_one, one_mul, abs_of_pos (by linarith : (0 : ℝ) < x)]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
    ⟨0, 5, 0, by norm_num, fun x _ c hc => by
      have hx := hx1 x c hc
      have hx0 : 0 < x := by linarith
      obtain ⟨rfl, -⟩ := hmem x c hc
      have hLl : 0 ≤ Ll x := by simp only [Ll]; positivity
      have hn := p4_eval_norm (1 / 4) 4 (Ll x)
      have hu := p4_upper (Ll x) hLl
      have hp : pnorm (longDP (1 / 4) 4 (Ll x)) (p4Cfg x) 4 =
          ‖(longDP (1 / 4) 4 (Ll x)).eval (1 : DirichletCharacter ℂ 1) (half 0)‖ := by
        unfold pnorm
        simp only [p4Cfg, Finset.sum_singleton]
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
        exact Real.rpow_rpow_inv (norm_nonneg _) (by norm_num)
      have hq : (((p4Cfg x).q : ℝ) * (p4Cfg x).T) ^ (1 / 4 : ℝ) = Ll x := by
        simp only [p4Cfg, Nat.cast_one, one_mul, Ll, abs_of_pos hx0]
        rw [← Real.rpow_mul hx0.le]; norm_num
      have hL1 : 1 ≤ Ll x := by
        simp only [Ll, abs_of_pos hx0]; exact Real.one_le_rpow hx (by norm_num)
      rw [hp, hq, Real.rpow_zero, one_mul, hn]
      linarith⟩
  obtain ⟨C, X0, hC⟩ := hcfg 1 one_pos
  -- a large x where the single point is admissible
  have ev1 : ∀ᶠ x : ℝ in atTop, 2 < x ^ (0.4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_gt_atTop 2
  have ev2 : ∀ᶠ x : ℝ in atTop, 4 ≤ x ^ (0.6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 4
  have ev3 : ∀ᶠ x : ℝ in atTop, 27 * |C| + 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have ev4 : ∀ᶠ x : ℝ in atTop, max X0 4 ≤ x := eventually_ge_atTop _
  obtain ⟨x, h1, h2, h3, h4⟩ := (ev1.and (ev2.and (ev3.and ev4))).exists
  have hx4 : 4 ≤ x := (le_max_right _ _).trans h4
  have hx0 : 0 < x := by linarith
  have hxX : X0 ≤ x := (le_max_left _ _).trans h4
  have hstd : (p4Cfg x).Std x := by
    refine ⟨?_, le_refl _, by simp only [p4Cfg, Nat.cast_one]; linarith, h1, ?_⟩
    · intro e he
      have he1 : e = ((0 : ℝ), (1 : DirichletCharacter ℂ 1)) := Finset.mem_singleton.1 he
      refine ⟨by rw [he1]; show |(0:ℝ)| ≤ x ^ (0.4:ℝ); rw [abs_zero]; linarith, ?_⟩
      intro e' he' _ hne
      have he2 : e' = ((0 : ℝ), (1 : DirichletCharacter ℂ 1)) := Finset.mem_singleton.1 he'
      exact absurd (he1.trans he2.symm) hne
    · have : x = x ^ (0.4 : ℝ) * x ^ (0.6 : ℝ) := by
        rw [← Real.rpow_add hx0]; norm_num
      show x ^ (0.4 : ℝ) ≤ x / 4
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [Real.rpow_pos_of_pos hx0 (0.4 : ℝ)]
  have hb := hC x hxX (p4Cfg x) ⟨rfl, hstd⟩
  -- lower bound for the product
  have hMl : Ml x = x ^ (0.45 : ℝ) := by simp only [Ml, abs_of_pos hx0]
  have hLl : Ll x = x ^ (0.1 : ℝ) := by simp only [Ll, abs_of_pos hx0]
  have hNl := hpos x hx0
  have hge1 : ∀ y : ℝ, 0 ≤ y → 1 ≤ x ^ y := fun y hy => Real.one_le_rpow (by linarith) hy
  have eM := p4_lower (Ml x) (by rw [hMl]; exact hge1 _ (by norm_num))
  have eN := p4_lower (Nl x) (by rw [hNl]; exact hge1 _ (by norm_num))
  have eL := p4_lower (Ll x) (by rw [hLl]; exact hge1 _ (by norm_num))
  rw [← p4_eval_norm] at eM eN eL
  have hnorm : norm1prod [longDP (1 / 4) 4 (Ml x), longDP (1 / 4) 4 (Nl x),
      (⟨fun _ => 1, Finset.Ioo ⌊(1 / 4 : ℝ) * Ll x⌋₊ ⌈4 * Ll x⌉₊⟩ : DP)] (p4Cfg x) =
      ‖(longDP (1 / 4) 4 (Ml x)).eval (1 : DirichletCharacter ℂ 1) (half 0)‖ *
      ‖(longDP (1 / 4) 4 (Nl x)).eval (1 : DirichletCharacter ℂ 1) (half 0)‖ *
      ‖(longDP (1 / 4) 4 (Ll x)).eval (1 : DirichletCharacter ℂ 1) (half 0)‖ := by
    unfold norm1prod
    simp only [p4Cfg, Finset.sum_singleton, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, norm_mul, longDP]
    ring
  have hsq : √(Ml x) * √(Nl x) * √(Ll x) = √x := by
    rw [← Real.sqrt_mul (by rw [hMl]; positivity), ← Real.sqrt_mul (by rw [hMl, hNl]; positivity)]
    congr 1
    exact hprod x
  have hlow : √x / 27 ≤ norm1prod [longDP (1 / 4) 4 (Ml x), longDP (1 / 4) 4 (Nl x),
      (⟨fun _ => 1, Finset.Ioo ⌊(1 / 4 : ℝ) * Ll x⌋₊ ⌈4 * Ll x⌉₊⟩ : DP)] (p4Cfg x) := by
    rw [hnorm, ← hsq]
    have a1 : 0 ≤ √(Ml x) / 3 := by positivity
    have a2 : 0 ≤ √(Nl x) / 3 := by positivity
    calc √(Ml x) * √(Nl x) * √(Ll x) / 27 = (√(Ml x) / 3) * (√(Nl x) / 3) * (√(Ll x) / 3) := by
          ring
      _ ≤ _ := mul_le_mul (mul_le_mul eM eN a2 (a1.trans eM)) eL (by positivity)
          (mul_nonneg (a1.trans eM) (a2.trans eN))
  have hlog : 0 < Real.log x := by linarith [abs_nonneg C]
  have hsx : 0 < √x := Real.sqrt_pos.2 hx0
  have hb' : √x / 27 ≤ C * √x / Real.log x := by
    have := hlow.trans hb
    simpa [L, Real.rpow_one, Real.sqrt_eq_rpow] using this
  rw [le_div_iff₀ hlog] at hb'
  have : √x / 27 * Real.log x ≥ √x / 27 * (27 * |C| + 1) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have hC' : C * √x ≤ |C| * √x := mul_le_mul_of_nonneg_right (le_abs_self C) hsx.le
  nlinarith

#print axioms p4_chi_one
#print axioms p4_eval_norm
#print axioms p4_hasLen
#print axioms p4_coef
#print axioms p4_lower
#print axioms p4_upper
#print axioms leaf_339_lemma4_variant_false

end LeanLab.BakerHarmanPintz1997
