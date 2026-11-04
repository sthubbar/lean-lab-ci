import LeanLab.Grimmelt2019.Prop21
import Mathlib.Analysis.Fourier.FourierTransform

namespace LeanLab.Grimmelt2019.DecompJ227WIP2

open LeanLab.Grimmelt2019.Prop21
open MeasureTheory

noncomputable section

/-! ### 0. Degenerate values of `Δ` -/

/-- A negative `Δ` makes `FourierClose` unsatisfiable, so the leaf has no counterexample with
`Δ < 0`: `Δ ≥ 0` follows from the hypotheses. -/
theorem fourierClose_delta_nonneg {S : Finset ℤ} {g : ℤ → ℝ} {H Δ : ℝ} (hH : 1 ≤ H)
    (h : FourierClose S H Δ g) : 0 ≤ Δ := by
  have hH0 : 0 < H := by linarith
  have h2 : -(1 / H) ≤ 1 / H := by
    have : 0 < 1 / H := by positivity
    linarith
  have h3 : 0 ≤ ∫ β in (-(1 / H))..(1 / H), ‖fhat S g (0 + β)‖ ^ 2 :=
    intervalIntegral.integral_nonneg h2 (fun x _ => by positivity)
  have h4 := h 0
  simpa using le_trans h3 h4

/-! ### 1. Characters `e(α n) = exp (2 π i α n)`, written out -/

/-- `‖1 - e(θ)‖² = 4 sin²(πθ)`. -/
theorem norm_one_sub_exp (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))‖ ^ 2
      = 4 * Real.sin (Real.pi * θ) ^ 2 := by
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))
      = Complex.exp (((2 * Real.pi * θ : ℝ)) * Complex.I) := by
    congr 1; push_cast; ring
  rw [hexp, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hre : (Complex.exp (((2 * Real.pi * θ : ℝ)) * Complex.I)).re = Real.cos (2 * Real.pi * θ) :=
    Complex.exp_ofReal_mul_I_re _
  have him : (Complex.exp (((2 * Real.pi * θ : ℝ)) * Complex.I)).im = Real.sin (2 * Real.pi * θ) :=
    Complex.exp_ofReal_mul_I_im _
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
  have h2 : Real.cos (2 * Real.pi * θ) = 1 - 2 * Real.sin (Real.pi * θ) ^ 2 := by
    have h := Real.cos_two_mul' (Real.pi * θ)
    rw [show 2 * (Real.pi * θ) = 2 * Real.pi * θ from by ring] at h
    have h3 := Real.sin_sq_add_cos_sq (Real.pi * θ)
    nlinarith [h, h3]
  have h3 : Real.sin (2 * Real.pi * θ) = 2 * Real.sin (Real.pi * θ) * Real.cos (Real.pi * θ) := by
    have h := Real.sin_two_mul (Real.pi * θ)
    rw [show 2 * (Real.pi * θ) = 2 * Real.pi * θ from by ring] at h
    linarith [h]
  have h4 := Real.sin_sq_add_cos_sq (Real.pi * θ)
  rw [h2, h3]
  nlinarith [h4]

/-- `2t ≤ sin (πt)` on `[0, 1/2]`. -/
theorem two_mul_le_sin_pi {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    2 * t ≤ Real.sin (Real.pi * t) := by
  have hx0 : 0 ≤ Real.pi * t := by positivity
  have hx1 : Real.pi * t ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin hx0 hx1
  rw [show 2 / Real.pi * (Real.pi * t) = 2 * t from by field_simp] at h
  exact h

/-- The exponential character `e (α n) = exp (2 π i α n)`. -/
theorem conj_exp_char (α : ℝ) (n : ℤ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  have hn : ((n : ℤ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
  have hnn : ((-n : ℤ) : ℂ) = ((-(n : ℝ)) : ℂ) := by push_cast; ring
  rw [hn, hnn]
  simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem mul_exp_char (α : ℝ) (m n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
        * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((m + n : ℤ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem three_exp_char (α : ℝ) (m k n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
        * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ))
        * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((m + k - n : ℤ) : ℂ)) := by
  rw [mul_exp_char α m k, mul_exp_char α (m + k) (-n),
    show ((m + k) + (-n) : ℤ) = m + k - n from by omega]

/-- `e^{-1}(n) = e(-n)`. -/
theorem inv_exp_char (α : ℝ) (n : ℤ) :
    (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)))⁻¹
      = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ)) := by
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_exp_char (α : ℝ) (n : ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)
      = ((2 * Real.pi * α * n : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_exp_char (n : ℤ) :
    Continuous fun α : ℝ => Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) := by
  have h : Continuous fun α : ℝ => (2 * Real.pi * Complex.I * (n : ℂ)) * (α : ℂ) := by fun_prop
  refine (Complex.continuous_exp.comp h).congr (fun α => ?_)
  simp only [Function.comp_apply]
  congr 1; ring

/-- Orthogonality `∫_0^1 e(α k) dα = [k = 0]`. -/
theorem integral_exp_char_sub (k : ℤ) :
    (∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ)))
      = if k = 0 then 1 else 0 := by
  have hpt : ∀ α : ℝ, Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ))
      = Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * (α : ℂ)) := by
    intro α; congr 1; ring
  simp_rw [hpt]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk, integral_exp_mul_complex]
    · have e1 : Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * 1) = 1 := by
        rw [mul_one]
        have h : 2 * Real.pi * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
        rw [h, Complex.exp_int_mul_two_pi_mul_I]
      have e0 : Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * 0) = 1 := by simp
      rw [Complex.ofReal_one, Complex.ofReal_zero, e1, e0, sub_self, zero_div]
    · have hkC : ((k : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hkC

/-- `fhat` is the finite exponential sum. -/
theorem fhat_eq_sum' (S : Finset ℤ) (g : ℤ → ℝ) (α : ℝ) :
    fhat S g α = ∑ n ∈ S, (g n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) :=
  rfl

theorem continuous_fhat' (S : Finset ℤ) (g : ℤ → ℝ) :
    Continuous fun α : ℝ => fhat S g α := by
  have h : (fun α : ℝ => fhat S g α)
      = (fun α : ℝ => ∑ n ∈ S, (g n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))) := by
    funext α; exact fhat_eq_sum' S g α
  rw [h]
  exact continuous_finsetSum (M := ℂ) _ fun n _ => continuous_const.mul (continuous_exp_char n)

/- NOTE: the following two lemmas are drafted but did NOT reach a clean compile in this
   session, so they are not claimed:
     `plancherel : ∫ α in 0..1, Complex.normSq (fhat S f α) = sqn S f`
     `inversion  : ((conv S f g n : ℝ) : ℂ)
                     = ∫ α in 0..1, fhat S f α * fhat S g α * exp (2πiα(-n))   (SuppIn S g)`
   Both are finite exponential-sum computations: expand the product, use
   `integral_exp_char_sub` (proved below) and `Finset.sum_ite_eq'`. -/


/-- Pairing of two finite trigonometric polynomials. -/
theorem pairing_fhat (S : Finset ℤ) (f g : ℤ → ℝ) :
    (∫ α in (0 : ℝ)..1, fhat S f α * (starRingEnd ℂ) (fhat S g α))
      = ((∑ n ∈ S, f n * g n : ℝ) : ℂ) := by
  have hpair : ∀ α : ℝ, fhat S f α * (starRingEnd ℂ) (fhat S g α)
      = ∑ m ∈ S, ∑ k ∈ S, ((f m * g k : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((m - k : ℤ) : ℂ)) := by
    intro α
    simp only [fhat_eq_sum']
    have hc : (starRingEnd ℂ)
        (∑ n ∈ S, (g n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)))
        = ∑ n ∈ S, (g n : ℂ)
            * (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [map_mul, Complex.conj_ofReal]
    rw [hc, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    rw [conj_exp_char,
      show ((-k : ℤ)) = -k from rfl]
    have h2 : ((f m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ)))
        * ((g k : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-k : ℤ) : ℂ)))
        = ((f m * g k : ℝ) : ℂ)
          * (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-k : ℤ) : ℂ))) := by
      push_cast; ring
    rw [h2, mul_exp_char α m (-k), show ((m + -k : ℤ)) = m - k from by ring]
  have hInt : IntervalIntegrable
      (fun α : ℝ => fhat S f α * (starRingEnd ℂ) (fhat S g α)) volume 0 1 :=
    ((continuous_fhat' S f).mul (Complex.continuous_conj.comp (continuous_fhat' S g))).intervalIntegrable _ _
  have hpt : ∀ α : ℝ, fhat S f α * (starRingEnd ℂ) (fhat S g α)
      = ∑ m ∈ S, ∑ k ∈ S, ((f m * g k : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((m - k : ℤ) : ℂ)) := hpair
  rw [intervalIntegral.integral_congr (fun α _ => hpt α)]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Complex.ofReal_sum (s := S) (f := fun n => f n * g n)]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_eq_single m]
      · rw [intervalIntegral.integral_const_mul, integral_exp_char_sub, sub_self, if_pos rfl, mul_one]
      · intro k _ hne
        have h' : ¬ (m - k = 0) := by omega
        rw [intervalIntegral.integral_const_mul, integral_exp_char_sub]
        simp only [h', ite_false, mul_zero]
      · intro hnot; exact absurd hm hnot
    · intro k _
      exact (continuous_const.mul (continuous_exp_char (m - k))).intervalIntegrable _ _
  · intro m _
    exact ((continuous_finsetSum (M := ℂ) _
      (fun k _ => continuous_const.mul (continuous_exp_char (m - k)))).intervalIntegrable _ _)

/-- Plancherel for finite trigonometric polynomials: `∫_0^1 ‖fhat S f‖² = sqn S f`. -/
theorem plancherel (S : Finset ℤ) (f : ℤ → ℝ) :
    (∫ α in (0 : ℝ)..1, Complex.normSq (fhat S f α)) = sqn S f := by
  have hInt : IntervalIntegrable
      (fun α : ℝ => fhat S f α * (starRingEnd ℂ) (fhat S f α)) volume 0 1 :=
    ((continuous_fhat' S f).mul (Complex.continuous_conj.comp (continuous_fhat' S f))).intervalIntegrable _ _
  have hpt : ∀ α : ℝ, Complex.normSq (fhat S f α)
      = Complex.reCLM (fhat S f α * (starRingEnd ℂ) (fhat S f α)) := by
    intro α
    rw [Complex.reCLM_apply, Complex.mul_conj]
    simp
  rw [intervalIntegral.integral_congr (fun α _ => hpt α)]
  rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hInt]
  rw [pairing_fhat]
  simp [sqn, pow_two]


/- NOTE: Fourier inversion
     `((conv S f g n : ℝ) : ℂ) = ∫ α in 0..1, fhat S f α * fhat S g α * e(-αn)   (SuppIn S g)`
   is drafted but did NOT reach a clean compile here (a type-inference ambiguity in the
   expansion of the product of the two finite exponential sums); it is not claimed. -/

/-- `∑_{k=-c}^{c} g k = g 0 + ∑_{i<c} (g (i+1) + g (-(i+1)))`. -/
theorem icc_split_sum (c : ℕ) (g : ℤ → ℂ) :
    (∑ k ∈ Finset.Icc (-(c:ℤ)) (c:ℤ), g k)
      = g 0 + ∑ i ∈ Finset.range c, (g ((i:ℤ)+1) + g (-((i:ℤ)+1))) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hset : Finset.Icc (-(((c+1 : ℕ)) : ℤ)) (((c+1 : ℕ)) : ℤ)
        = insert (-(((c+1 : ℕ)) : ℤ))
            (insert (((c+1 : ℕ)) : ℤ) (Finset.Icc (-(c:ℤ)) (c:ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      constructor
      · rintro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h2 with h | h
        · exact Or.inr (Or.inl (by omega))
        · rcases eq_or_lt_of_le h1 with h' | h'
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inr (by omega))
      · rintro (h | h | h) <;> omega
    rw [hset]
    have h1 : (-(((c+1 : ℕ)) : ℤ)) ∉
        insert (((c+1 : ℕ)) : ℤ) (Finset.Icc (-(c:ℤ)) (c:ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    have h2 : (((c+1 : ℕ)) : ℤ) ∉ Finset.Icc (-(c:ℤ)) (c:ℤ) := by
      simp only [Finset.mem_Icc]; push_cast; omega
    rw [Finset.sum_insert h1, Finset.sum_insert h2, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- The geometric sum bound: `‖∑_{j<M} z^j‖ ‖1 - z‖ ≤ 2` for `‖z‖ = 1`. -/
theorem geom_norm_le (z : ℂ) (hz : ‖z‖ = 1) (M : ℕ) :
    ‖∑ j ∈ Finset.range M, z ^ j‖ * ‖1 - z‖ ≤ 2 := by
  have hg : (∑ j ∈ Finset.range M, z ^ j) * (z - 1) = z ^ M - 1 := geom_sum_mul z M
  have hnorm : ‖∑ j ∈ Finset.range M, z ^ j‖ * ‖1 - z‖ = ‖z ^ M - 1‖ := by
    rw [show ‖1 - z‖ = ‖z - 1‖ from by rw [← norm_neg]; congr 1; ring, ← hg, norm_mul]
  rw [hnorm]
  calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow]; norm_num


/-- **The coarse global-energy bound provably cannot close the leaf.** With `S = {0}`,
`g = δ₀` (so `fhat S g ≡ 1`) and `H = 3` the local Fourier energy is `2/H = 2/3`, while
`sqn S g = 1`; so `FourierClose` does not imply `sqn S g ≤ Δ`, and the bound
`∑_{n ∈ win} conv² ≤ 2H ‖f‖² sqn S g` (the lab's `CoarseSecondMoment`, no `sorry`) is a factor
`H` too weak to reach the leaf. -/
theorem fourierClose_delta_lt_sqn :
    FourierClose ({0} : Finset ℤ) 3 (2 / 3) (fun n => if n = 0 then (1 : ℝ) else 0) ∧
      ¬ (sqn ({0} : Finset ℤ) (fun n => if n = 0 then (1 : ℝ) else 0) ≤ 2 / 3) := by
  constructor
  · intro α
    have hf : ∀ β : ℝ, fhat ({0} : Finset ℤ) (fun n => if n = 0 then (1 : ℝ) else 0) (α + β) = 1 := by
      intro β
      rw [fhat_eq_sum']
      simp
    have h1 : (∫ β in (-(1 / 3 : ℝ))..(1 / 3),
        ‖fhat ({0} : Finset ℤ) (fun n => if n = 0 then (1 : ℝ) else 0) (α + β)‖ ^ 2)
        = ∫ _β in (-(1 / 3 : ℝ))..(1 / 3), (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun β _ => ?_
      rw [hf β]
      norm_num
    rw [h1, intervalIntegral.integral_const]
    norm_num
  · intro h
    have h1 : sqn ({0} : Finset ℤ) (fun n => if n = 0 then (1 : ℝ) else 0) = 1 := by
      simp [sqn]
    rw [h1] at h
    norm_num at h


/-! ### The tent sum: `∑_{|k|<M} (M-|k|) z^k` equals `‖∑_{j<M} z^j‖²` -/

/-- `(∑_{j≤m} z^j) (z^{m+1})⁻¹ = ∑_{i≤m} (z^{i+1})⁻¹`. -/
theorem hcross1 (z : ℂ) (hz : z ≠ 0) (m : ℕ) :
    (∑ j ∈ Finset.range (m+1), z ^ j) * (z ^ (m+1))⁻¹
      = ∑ i ∈ Finset.range (m+1), (z ^ (i+1))⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hL : (∑ j ∈ Finset.range (m+1+1), z ^ j) * (z ^ (m+1+1))⁻¹
        = ((∑ j ∈ Finset.range (m+1), z ^ j) * (z ^ (m+1))⁻¹) * z⁻¹ + z⁻¹ := by
      have hp : z ^ (m+1+1) = z ^ (m+1) * z := pow_succ z (m+1)
      have h1 : z ^ (m+1) * (z ^ (m+1))⁻¹ = (1 : ℂ) :=
        mul_inv_cancel₀ (pow_ne_zero (m+1) hz)
      rw [Finset.sum_range_succ, add_mul, hp, mul_inv,
        show z ^ (m+1) * ((z ^ (m+1))⁻¹ * z⁻¹)
            = (z ^ (m+1) * (z ^ (m+1))⁻¹) * z⁻¹ from by ring, h1, one_mul]
      ring
    have hR := Finset.sum_range_succ' (f := fun i => (z ^ (i+1))⁻¹) (n := m+1)
    have hpt : ∀ i ∈ Finset.range (m+1), (z ^ (i+1))⁻¹ * z⁻¹ = (z ^ ((i+1)+1))⁻¹ := by
      intro i _
      have hp : z ^ (i+1) * z = z ^ ((i+1)+1) := pow_succ z (i+1) |>.symm
      rw [show (z ^ (i+1))⁻¹ * z⁻¹ = (z ^ (i+1) * z)⁻¹ from by rw [mul_inv], hp]
    rw [hL, hR, ih, Finset.sum_mul]
    rw [Finset.sum_congr rfl hpt]
    norm_num

/-- `z^{m+1} ∑_{j≤m} (z^j)⁻¹ = ∑_{i≤m} z^{i+1}`. -/
theorem hcross2 (z : ℂ) (hz : z ≠ 0) (m : ℕ) :
    z ^ (m+1) * (∑ j ∈ Finset.range (m+1), (z ^ j)⁻¹)
      = ∑ i ∈ Finset.range (m+1), z ^ (i+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hL : z ^ (m+1+1) * (∑ j ∈ Finset.range (m+1+1), (z ^ j)⁻¹)
        = z * (z ^ (m+1) * (∑ j ∈ Finset.range (m+1), (z ^ j)⁻¹)) + z := by
      have h1 : z ^ (m+1+1) * (z ^ (m+1))⁻¹ = z := by
        rw [pow_succ', mul_assoc, mul_inv_cancel₀ (pow_ne_zero (m+1) hz), mul_one]
      rw [Finset.sum_range_succ, mul_add, h1, pow_succ', mul_assoc]
    have hR := Finset.sum_range_succ' (f := fun i => z ^ (i+1)) (n := m+1)
    have hpt : ∀ i ∈ Finset.range (m+1), z * z ^ (i+1) = z ^ ((i+1)+1) := by
      intro i _
      rw [show z ^ ((i+1)+1) = z * z ^ (i+1) from pow_succ' z (i+1)]
    rw [hL, hR, ih, Finset.mul_sum]
    rw [Finset.sum_congr rfl hpt]
    norm_num

/-- The tent sum is the squared modulus of the geometric sum. -/
theorem j227_tent (z : ℂ) (hz : z ≠ 0) (m : ℕ) :
    (∑ j ∈ Finset.range (m+1), z ^ j) * (∑ j ∈ Finset.range (m+1), (z ^ j)⁻¹)
      = ((m+1 : ℕ) : ℂ)
        + ∑ i ∈ Finset.range m, (((m-i : ℕ) : ℂ) * (z ^ (i+1) + (z ^ (i+1))⁻¹)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := hcross1 z hz m
    have h2 := hcross2 z hz m
    have hR : (∑ i ∈ Finset.range (m+1), (((m+1-i : ℕ) : ℂ)
          * (z ^ (i+1) + (z ^ (i+1))⁻¹)))
        = (∑ i ∈ Finset.range m, (((m-i : ℕ) : ℂ) * (z ^ (i+1) + (z ^ (i+1))⁻¹)))
          + (∑ i ∈ Finset.range m, (z ^ (i+1) + (z ^ (i+1))⁻¹))
          + (z ^ (m+1) + (z ^ (m+1))⁻¹) := by
      have hcoef : ∀ i ∈ Finset.range m,
          (((m+1-i : ℕ) : ℂ) * (z ^ (i+1) + (z ^ (i+1))⁻¹))
            = (((m-i : ℕ) : ℂ) * (z ^ (i+1) + (z ^ (i+1))⁻¹))
              + (z ^ (i+1) + (z ^ (i+1))⁻¹) := by
        intro i hi
        have hi' : i < m := by simpa using hi
        have hc : (m+1-i : ℕ) = (m-i : ℕ) + 1 := by omega
        rw [hc]
        push_cast
        ring
      rw [Finset.sum_range_succ (n := m), Finset.sum_congr rfl hcoef, Finset.sum_add_distrib,
        Finset.sum_add_distrib, add_assoc]
      norm_num
      abel
    have hA : (∑ i ∈ Finset.range (m+1), (z ^ (i+1))⁻¹)
        = (∑ i ∈ Finset.range m, (z ^ (i+1))⁻¹) + (z ^ (m+1))⁻¹ := by
      rw [Finset.sum_range_succ]
    have hB : (∑ i ∈ Finset.range (m+1), z ^ (i+1))
        = (∑ i ∈ Finset.range m, z ^ (i+1)) + z ^ (m+1) := by
      rw [Finset.sum_range_succ]
    have hS : (∑ j ∈ Finset.range (m+1+1), z ^ j)
        = (∑ j ∈ Finset.range (m+1), z ^ j) + z ^ (m+1) := by rw [Finset.sum_range_succ]
    have hT : (∑ j ∈ Finset.range (m+1+1), (z ^ j)⁻¹)
        = (∑ j ∈ Finset.range (m+1), (z ^ j)⁻¹) + (z ^ (m+1))⁻¹ := by
      rw [Finset.sum_range_succ]
    rw [hS, hT, add_mul, mul_add, mul_add, ih, h1, h2, hR, hA, hB,
      Finset.sum_add_distrib]
    have hz2 : z ^ (m+1) * (z ^ (m+1))⁻¹ = (1 : ℂ) :=
      mul_inv_cancel₀ (pow_ne_zero (m+1) hz)
    rw [hz2]
    push_cast
    ring


/-! ### The two bounds on the tent kernel -/

/-- `|W| ≤ 2M` for `W = E · (2/M) · (∑ z^j)(∑ (z^j)⁻¹)` with `‖E‖ = ‖z‖ = 1`. -/
theorem W_norm_le (E z : ℂ) (hE : ‖E‖ = 1) (hz : ‖z‖ = 1) (M : ℕ) (hM : 1 ≤ M) :
    ‖E * ((2/(M:ℝ) : ℝ) : ℂ)
        * ((∑ j ∈ Finset.range M, z ^ j) * (∑ j ∈ Finset.range M, (z ^ j)⁻¹))‖
      ≤ 2 * (M:ℝ) := by
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hS : ‖∑ j ∈ Finset.range M, z ^ j‖ ≤ (M:ℝ) := by
    calc ‖∑ j ∈ Finset.range M, z ^ j‖ ≤ ∑ j ∈ Finset.range M, ‖z ^ j‖ := norm_sum_le _ _
      _ = ∑ _j ∈ Finset.range M, (1:ℝ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_pow, hz, one_pow]
      _ = (M:ℝ) := by simp
  have hT : ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖ ≤ (M:ℝ) := by
    calc ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖
        ≤ ∑ j ∈ Finset.range M, ‖(z ^ j)⁻¹‖ := norm_sum_le _ _
      _ = ∑ _j ∈ Finset.range M, (1:ℝ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_inv, norm_pow, hz, one_pow, inv_one]
      _ = (M:ℝ) := by simp
  rw [norm_mul, norm_mul, hE, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 2/(M:ℝ)), norm_mul]
  calc (2/(M:ℝ)) * (‖∑ j ∈ Finset.range M, z ^ j‖
        * ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖)
      ≤ (2/(M:ℝ)) * ((M:ℝ) * (M:ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hS hT (norm_nonneg _) (by positivity)
    _ = 2 * (M:ℝ) := by field_simp

/-- `|W(θ)| sin²(πθ) ≤ 2/M`: the decay that makes the kernel local at scale `1/M`. -/
theorem W_decay_le (E z : ℂ) (hE : ‖E‖ = 1) (hz : ‖z‖ = 1) (M : ℕ) (hM : 1 ≤ M) (θ : ℝ)
    (hsin : ‖1 - z‖ ^ 2 = 4 * Real.sin (Real.pi * θ) ^ 2) :
    ‖E * ((2/(M:ℝ) : ℝ) : ℂ)
        * ((∑ j ∈ Finset.range M, z ^ j) * (∑ j ∈ Finset.range M, (z ^ j)⁻¹))‖
        * Real.sin (Real.pi * θ) ^ 2 ≤ 2 / (M:ℝ) := by
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hS := geom_norm_le z hz M
  have hT : ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖ * ‖1 - z‖ ≤ 2 := by
    have hzi : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
    have h := geom_norm_le z⁻¹ hzi M
    have hinv : ∀ j : ℕ, (z⁻¹) ^ j = (z ^ j)⁻¹ := fun j => inv_pow z j
    have h1z : ‖1 - z⁻¹‖ = ‖1 - z‖ := by
      rw [show (1:ℂ) - z⁻¹ = z⁻¹ * (z - 1) from by field_simp]
      rw [norm_mul, norm_inv, hz, inv_one, one_mul]
      rw [show ‖z - 1‖ = ‖1 - z‖ from by rw [← norm_neg]; congr 1; ring]
    simpa only [hinv, h1z] using h
  have hkey : ‖∑ j ∈ Finset.range M, z ^ j‖ * ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖
      * ‖1 - z‖ ^ 2 ≤ 4 := by
    calc ‖∑ j ∈ Finset.range M, z ^ j‖ * ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖
          * ‖1 - z‖ ^ 2
        = (‖∑ j ∈ Finset.range M, z ^ j‖ * ‖1 - z‖)
          * (‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖ * ‖1 - z‖) := by ring
      _ ≤ 2 * 2 := mul_le_mul hS hT (by positivity) (by norm_num)
      _ = 4 := by norm_num
  have hST : ‖∑ j ∈ Finset.range M, z ^ j‖ * ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖
      * Real.sin (Real.pi * θ) ^ 2 ≤ 1 := by
    have h4 : ‖∑ j ∈ Finset.range M, z ^ j‖ * ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖
        * (4 * Real.sin (Real.pi * θ) ^ 2) ≤ 4 := by
      rw [← hsin]; exact hkey
    nlinarith [h4]
  rw [norm_mul, norm_mul, hE, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 2/(M:ℝ)), norm_mul]
  calc (2/(M:ℝ)) * (‖∑ j ∈ Finset.range M, z ^ j‖
        * ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖) * Real.sin (Real.pi * θ) ^ 2
      = (2/(M:ℝ)) * (‖∑ j ∈ Finset.range M, z ^ j‖
          * ‖∑ j ∈ Finset.range M, (z ^ j)⁻¹‖ * Real.sin (Real.pi * θ) ^ 2) := by ring
    _ ≤ (2/(M:ℝ)) * 1 := by
        refine mul_le_mul_of_nonneg_left hST (by positivity)
    _ = 2 / (M:ℝ) := by ring


/-! ### The transform of the tent weight -/

/-- `e(θ)^j = e(θ j)` for `j : ℕ`. -/
theorem exp_char_pow (θ : ℝ) (j : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ))) ^ j
      = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (j:ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The transform of the tent weight.** With `c_i = 2 (1 - (i+1)/M)` and `z = e(θ)`,
`2 + ∑_{i<M-1} c_i (e(θ(x₀+i+1)) + e(θ(x₀-i-1))) = e(θx₀) (2/M) (∑_{j<M} z^j)(∑_{j<M} (z^j)⁻¹)`. -/
theorem tent_transform (x₀ : ℤ) (M : ℕ) (hM : 1 ≤ M) (θ : ℝ) :
    (2 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ))
      + ∑ i ∈ Finset.range (M-1),
          (((2 * (1 - ((i:ℝ)+1)/(M:ℝ)) : ℝ)) : ℂ)
            * (Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ + ((i:ℤ)+1) : ℤ):ℂ))
               + Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ - ((i:ℤ)+1) : ℤ):ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ)) * ((2/(M:ℝ) : ℝ) : ℂ)
        * ((∑ j ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (j:ℂ)))
          * (∑ j ∈ Finset.range M,
              (Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (j:ℂ)))⁻¹)) := by
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ)) with hz_def
  have hzp : ∀ j : ℕ, z ^ j = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (j:ℂ)) :=
    fun j => exp_char_pow θ j
  have hzt : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (((j:ℤ)):ℂ)) = z ^ j :=
    fun j => (hzp j).symm
  have hzb : z ≠ 0 := by rw [hz_def]; exact Complex.exp_ne_zero _
  -- the two shifted characters
  have hplus : ∀ i : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ + ((i:ℤ)+1) : ℤ):ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ)) * z ^ (i+1) := by
    intro i
    rw [show (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ + ((i:ℤ)+1) : ℤ):ℂ))
        = 2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ)
          + 2 * Real.pi * Complex.I * (θ:ℂ) * (((i:ℤ)+1 : ℤ):ℂ) from by push_cast; ring,
      Complex.exp_add,
      show (((i:ℤ)+1 : ℤ)) = ((i+1 : ℕ) : ℤ) from by push_cast; ring, hzt]
  have hminus : ∀ i : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ - ((i:ℤ)+1) : ℤ):ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ)) * (z ^ (i+1))⁻¹ := by
    intro i
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ - ((i:ℤ)+1) : ℤ):ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((-((i:ℤ)+1) : ℤ):ℂ)) := by
      rw [show (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ - ((i:ℤ)+1) : ℤ):ℂ))
          = 2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ)
            + 2 * Real.pi * Complex.I * (θ:ℂ) * ((-((i:ℤ)+1) : ℤ):ℂ) from by push_cast; ring,
        Complex.exp_add]
    have h2 : Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((-((i:ℤ)+1) : ℤ):ℂ))
        = (z ^ (i+1))⁻¹ := by
      have e1 : ((-((i:ℤ)+1) : ℤ) : ℂ) = -(((i+1 : ℕ)) : ℂ) := by push_cast; ring
      rw [e1, show 2 * Real.pi * Complex.I * (θ:ℂ) * (-(((i+1 : ℕ)) : ℂ))
          = -(2 * Real.pi * Complex.I * (θ:ℂ) * (((i+1 : ℕ)) : ℂ)) from by ring,
        Complex.exp_neg, ← hzp]
    rw [h1, h2]
  -- the tent identity with `m = M-1`
  have htent := j227_tent z hzb (M-1)
  rw [Nat.sub_add_cancel hM] at htent
  -- normalise both sums to the `z`-form
  have hL : (∑ i ∈ Finset.range (M-1),
        (((2 * (1 - ((i:ℝ)+1)/(M:ℝ)) : ℝ)) : ℂ)
          * (Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ + ((i:ℤ)+1) : ℤ):ℂ))
             + Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * ((x₀ - ((i:ℤ)+1) : ℤ):ℂ))))
      = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ))
        * ∑ i ∈ Finset.range (M-1),
            (((2 * (1 - ((i:ℝ)+1)/(M:ℝ)) : ℝ)) : ℂ) * (z ^ (i+1) + (z ^ (i+1))⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hplus i, hminus i]
    ring
  rw [hL]
  have hS : (∑ j ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (j:ℂ)))
      = ∑ j ∈ Finset.range M, z ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (hzp j).symm
  have hT : (∑ j ∈ Finset.range M,
        (Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (j:ℂ)))⁻¹)
      = ∑ j ∈ Finset.range M, (z ^ j)⁻¹ := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hzp]
  rw [hS, hT, htent]
  -- coefficient bookkeeping
  have hcoef : ∀ i ∈ Finset.range (M-1),
      (((2 * (1 - ((i:ℝ)+1)/(M:ℝ)) : ℝ)) : ℂ)
        = ((2/(M:ℝ) : ℝ) : ℂ) * (((M-1-i : ℕ) : ℂ)) := by
    intro i hi
    have hi' : i < M - 1 := Finset.mem_range.mp hi
    have hiM : i ≤ M - 1 := by omega
    have hcast : ((M-1-i : ℕ) : ℝ) = (M:ℝ) - ((i:ℝ)+1) := by
      rw [Nat.cast_sub hiM, Nat.cast_sub hM]
      push_cast
      ring
    have hreal : 2 * (1 - ((i:ℝ)+1)/(M:ℝ)) = (2/(M:ℝ)) * ((M-1-i : ℕ) : ℝ) := by
      rw [hcast]
      field_simp
    calc (((2 * (1 - ((i:ℝ)+1)/(M:ℝ)) : ℝ)) : ℂ)
        = (((2/(M:ℝ)) * ((M-1-i : ℕ) : ℝ) : ℝ) : ℂ) := by rw [hreal]
      _ = ((2/(M:ℝ) : ℝ) : ℂ) * (((M-1-i : ℕ) : ℂ)) := by push_cast; ring
  have hstep : ∀ i ∈ Finset.range (M-1),
      (((2 * (1 - ((i:ℝ)+1)/(M:ℝ)) : ℝ)) : ℂ) * (z ^ (i+1) + (z ^ (i+1))⁻¹)
        = (((2/(M:ℝ) : ℝ) : ℂ) * (((M-1-i : ℕ) : ℂ))) * (z ^ (i+1) + (z ^ (i+1))⁻¹) := by
    intro i hi
    rw [hcoef i hi]
  have hstep2 : ∀ i ∈ Finset.range (M-1),
      (((2/(M:ℝ) : ℝ) : ℂ) * (((M-1-i : ℕ) : ℂ))) * (z ^ (i+1) + (z ^ (i+1))⁻¹)
        = ((2/(M:ℝ) : ℝ) : ℂ) * ((((M-1-i : ℕ) : ℂ)) * (z ^ (i+1) + (z ^ (i+1))⁻¹)) := by
    intro i _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_congr rfl hstep2, ← Finset.mul_sum]
  set S : ℂ := ∑ i ∈ Finset.range (M-1),
      ((((M-1-i : ℕ) : ℂ)) * (z ^ (i+1) + (z ^ (i+1))⁻¹)) with hSdef
  have hMne : ((M:ℝ) : ℂ) ≠ 0 := by
    have hpos : (0:ℝ) < (M:ℝ) := hMpos
    exact_mod_cast (ne_of_gt hpos)
  have h2 : ((2/(M:ℝ) : ℝ) : ℂ) * (((M:ℝ)) : ℂ) = 2 := by
    push_cast
    field_simp
    exact div_self hMne
  have key : (2:ℂ) + ((2/(M:ℝ) : ℝ) : ℂ) * S
      = ((2/(M:ℝ) : ℝ) : ℂ) * ((((M:ℝ)) : ℂ) + S) := by
    rw [← h2]; ring
  calc (2:ℂ) * Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ))
        + Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ))
          * (((2/(M:ℝ) : ℝ) : ℂ) * S)
      = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ))
        * (2 + ((2/(M:ℝ) : ℝ) : ℂ) * S) := by ring
    _ = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ))
        * (((2/(M:ℝ) : ℝ) : ℂ) * ((((M:ℝ)) : ℂ) + S)) := by rw [key]
    _ = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (x₀:ℂ)) * ((2/(M:ℝ) : ℝ) : ℂ)
        * ((((M:ℝ)) : ℂ) + S) := by ring



/-! ### Fourier inversion for the truncated convolution -/

/-- The inner integral: for fixed `m`, expanding `fhat S g` leaves `e(α(m+k-n))`, whose
interval integral is `[m+k-n = 0]`. -/
theorem inversion_inner (S : Finset ℤ) (g : ℤ → ℝ) (m n : ℤ) :
    (∫ α in (0:ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
          * (fhat S g α * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ))))
      = ∑ k ∈ S, (g k : ℂ) * (if m + k - n = 0 then (1:ℂ) else 0) := by
  have hpt : ∀ α : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
        * (fhat S g α * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ)))
      = ∑ k ∈ S, (g k : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((m + k - n : ℤ) : ℂ)) := by
    intro α
    rw [fhat_eq_sum']
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
          * ((∑ k ∈ S, (g k : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ)))
            * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ)))
        = (∑ k ∈ S, (g k : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ)))
          * (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ))) := by ring
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h3 := three_exp_char α m k n
    calc ((g k : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ)))
          * (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ)))
        = (g k : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ))) := by ring
      _ = (g k : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((m + k - n : ℤ) : ℂ)) := by rw [h3]
  rw [intervalIntegral.integral_congr (fun α _ => hpt α)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_exp_char_sub]
  · intro k _
    exact (continuous_const.mul (continuous_exp_char (m + k - n))).intervalIntegrable _ _

/-- **Fourier inversion** for the truncated convolution, with `g` supported in `S`. -/
theorem inversion (S : Finset ℤ) (f g : ℤ → ℝ) (hg : SuppIn S g) (n : ℤ) :
    ((conv S f g n : ℝ) : ℂ)
      = ∫ α in (0 : ℝ)..1, fhat S f α * fhat S g α
          * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ)) := by
  set ch : ℤ → ℝ → ℂ := fun j α =>
    Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (j : ℂ)) with hch
  set Fi : ℤ → ℝ → ℂ := fun m α => ch m α * (fhat S g α * ch (-n) α) with hFi
  have hstep : ∀ α : ℝ, fhat S f α * fhat S g α * ch (-n) α
      = ∑ m ∈ S, (f m : ℂ) * Fi m α := by
    intro α
    rw [fhat_eq_sum']
    rw [show (∑ m ∈ S, (f m : ℂ) * ch m α) * fhat S g α * ch (-n) α
        = (∑ m ∈ S, (f m : ℂ) * ch m α) * (fhat S g α * ch (-n) α) from by ring,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by simp only [hFi]; ring
  have hcont : ∀ m : ℤ, Continuous (Fi m) := by
    intro m
    have hch1 : Continuous (ch m) := by rw [hch]; exact continuous_exp_char m
    have hchn : Continuous (ch (-n)) := by rw [hch]; exact continuous_exp_char (-n)
    rw [hFi]
    simp only []
    exact hch1.mul ((continuous_fhat' S g).mul hchn)
  have houter : (∫ α in (0:ℝ)..1, fhat S f α * fhat S g α * ch (-n) α)
      = ∑ m ∈ S, (f m : ℂ) * ∫ α in (0:ℝ)..1, Fi m α := by
    rw [intervalIntegral.integral_congr (fun α _ => hstep α)]
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun m _ => by rw [intervalIntegral.integral_const_mul]
    · intro m _
      exact ((hcont m).const_mul ((f m : ℂ))).intervalIntegrable _ _
  have hinner : ∀ m : ℤ, (∫ α in (0:ℝ)..1, Fi m α)
      = ∑ k ∈ S, (g k : ℂ) * (if m + k - n = 0 then (1:ℂ) else 0) := by
    intro m
    have hpt : ∀ α : ℝ, Fi m α
        = ∑ k ∈ S, (g k : ℂ) * ch (m + k - n) α := by
      intro α
      rw [hFi]
      simp only []
      rw [hch]
      simp only []
      rw [fhat_eq_sum']
      rw [show ch m α * ((∑ k ∈ S, (g k : ℂ) * ch k α) * ch (-n) α)
          = (∑ k ∈ S, (g k : ℂ) * ch k α) * (ch m α * ch (-n) α) from by rw [hch]; ring,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hch]
      simp only []
      have h3 := three_exp_char α m k n
      calc ((g k : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ)))
            * (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ)))
          = (g k : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (m : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((-n : ℤ) : ℂ))) := by ring
        _ = (g k : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * (α : ℂ) * ((m + k - n : ℤ) : ℂ)) := by
            rw [h3]
    rw [intervalIntegral.integral_congr (fun α _ => hpt α)]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [hch]
      exact integral_exp_char_sub (m + k - n)
    · intro k _
      exact (continuous_const.mul (by rw [hch]; exact continuous_exp_char (m + k - n))).intervalIntegrable _ _
  rw [show ((conv S f g n : ℝ) : ℂ) = ∑ m ∈ S, ((f m * g (n - m) : ℝ) : ℂ) from by
    unfold conv
    rw [Complex.ofReal_sum]]
  rw [houter]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hinner m]
  rw [Finset.sum_eq_single (n - m)]
  · rw [if_pos (by ring), mul_one]
    push_cast
    ring
  · intro k _ hk
    have h2 : ¬ (m + k - n = 0) := by omega
    simp [h2]
  · intro hnot
    simp [hg (n - m) hnot]


/-! ### The convolution square as a double integral, and the master identity -/

/-- Conjugation commutes with the interval integral. -/
theorem interval_conj (F : ℝ → ℂ) (a b : ℝ) :
    (starRingEnd ℂ) (∫ x in a..b, F x) = ∫ x in a..b, (starRingEnd ℂ) (F x) := by
  rcases le_total a b with h | h
  · rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h]
    exact (integral_conj (𝕜 := ℂ) (f := F) (μ := volume.restrict (Set.Ioc a b))).symm
  · rw [intervalIntegral.integral_of_ge h, intervalIntegral.integral_of_ge h, map_neg, neg_inj]
    exact (integral_conj (𝕜 := ℂ) (f := F) (μ := volume.restrict (Set.Ioc b a))).symm

/-- A product of two interval integrals over `[0,1]` is an iterated integral. -/
theorem double_mul (A B : ℝ → ℂ) :
    (∫ x in (0:ℝ)..1, A x) * (∫ y in (0:ℝ)..1, B y)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, A x * B y := by
  rw [show (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, A x * B y)
      = ∫ x in (0:ℝ)..1, A x * (∫ y in (0:ℝ)..1, B y) from by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [intervalIntegral.integral_const_mul]]
  rw [intervalIntegral.integral_mul_const]

/-- The square of the convolution at `n`, as a double integral. -/
theorem conv_sq_double (S : Finset ℤ) (f g : ℤ → ℝ) (hg : SuppIn S g) (n : ℤ) :
    ((conv S f g n ^ 2 : ℝ) : ℂ)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
          (fhat S f x * fhat S g x)
            * (starRingEnd ℂ) (fhat S f y * fhat S g y)
            * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * ((-n : ℤ):ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * (y:ℂ) * (n:ℂ)) := by
  have h1 := inversion S f g hg n
  have h2 : ((conv S f g n : ℝ) : ℂ)
      = ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (fhat S f y * fhat S g y
          * Complex.exp (2 * Real.pi * Complex.I * (y:ℂ) * ((-n : ℤ):ℂ))) := by
    calc ((conv S f g n : ℝ) : ℂ)
        = (starRingEnd ℂ) ((conv S f g n : ℝ) : ℂ) := (Complex.conj_ofReal _).symm
      _ = (starRingEnd ℂ) (∫ y in (0:ℝ)..1, fhat S f y * fhat S g y
            * Complex.exp (2 * Real.pi * Complex.I * (y:ℂ) * ((-n : ℤ):ℂ))) := by
            rw [← h1]
      _ = _ := interval_conj _ _ _
  rw [show ((conv S f g n ^ 2 : ℝ) : ℂ)
      = ((conv S f g n : ℝ) : ℂ) * ((conv S f g n : ℝ) : ℂ) from by push_cast; ring]
  nth_rw 1 [h1]
  rw [h2, double_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [map_mul, Complex.conj_ofReal, conj_exp_char]
  ring


/-! ### The master identity: the weighted sum as a double integral -/

/-- **The integral algebra of the master identity.** For a character `ch` that is
multiplicative in its first argument, the weighted sum of the products
`(∫ x, A x ch(-x) n)(∫ y, B y ch y n)` is the double integral against the kernel `W`. -/
theorem weighted_sum_double {R : Finset ℤ} (A B : ℝ → ℂ) (w : ℤ → ℝ) (W : ℝ → ℂ)
    (ch : ℝ → ℤ → ℂ)
    (hchc : ∀ n : ℤ, Continuous fun θ : ℝ => ch θ n)
    (hchadd : ∀ x y : ℝ, ∀ n : ℤ, ch (y - x) n = ch y n * ch (-x) n)
    (hW : ∀ θ : ℝ, W θ = ∑ n ∈ R, (w n : ℂ) * ch θ n)
    (hAc : Continuous A) (hBc : Continuous B) :
    (∑ n ∈ R, (w n : ℂ)
        * ((∫ x in (0:ℝ)..1, A x * ch (-x) n) * (∫ y in (0:ℝ)..1, B y * ch y n)))
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, A x * B y * W (y - x) := by
  -- per `n`: the product of the two integrals is the double integral of the weighted integrand
  have hterm : ∀ n ∈ R, (w n : ℂ)
        * ((∫ x in (0:ℝ)..1, A x * ch (-x) n) * (∫ y in (0:ℝ)..1, B y * ch y n))
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, A x * B y * ((w n : ℂ) * ch (y - x) n) := by
    intro n _
    rw [double_mul (fun x : ℝ => A x * ch (-x) n) (fun y : ℝ => B y * ch y n)]
    have h1 : (w n : ℂ) * ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
          (A x * ch (-x) n) * (B y * ch y n)
        = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
          (w n : ℂ) * ((A x * ch (-x) n) * (B y * ch y n)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by
        rw [← intervalIntegral.integral_const_mul]
    rw [h1]
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hchadd x y n]
    ring
  -- the inner integral, written so that the `x`-dependence is manifestly continuous
  have hfac : ∀ n ∈ R, ∀ x : ℝ,
      (∫ y in (0:ℝ)..1, A x * B y * ((w n : ℂ) * ch (y - x) n))
        = (A x * (w n : ℂ) * ch (-x) n) * (∫ y in (0:ℝ)..1, B y * ch y n) := by
    intro n _ x
    rw [show (fun y : ℝ => A x * B y * ((w n : ℂ) * ch (y - x) n))
        = (fun y : ℝ => (A x * (w n : ℂ) * ch (-x) n) * (B y * ch y n)) from by
      funext y
      rw [hchadd x y n]
      ring,
      intervalIntegral.integral_const_mul]
  have hint : ∀ n ∈ R, IntervalIntegrable
      (fun x : ℝ => ∫ y in (0:ℝ)..1, A x * B y * ((w n : ℂ) * ch (y - x) n)) volume 0 1 := by
    intro n hn
    have hc : Continuous fun x : ℝ =>
        (A x * (w n : ℂ) * ch (-x) n) * (∫ y in (0:ℝ)..1, B y * ch y n) := by
      have h1 : Continuous fun x : ℝ => A x * (w n : ℂ) * ch (-x) n :=
        (hAc.mul continuous_const).mul ((hchc n).comp continuous_neg)
      exact h1.mul continuous_const
    exact (hc.congr fun x => (hfac n hn x).symm).intervalIntegrable _ _
  rw [Finset.sum_congr rfl hterm]
  rw [← intervalIntegral.integral_finsetSum (s := R)
    (f := fun n x => ∫ y in (0:ℝ)..1, A x * B y * ((w n : ℂ) * ch (y - x) n)) hint]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← intervalIntegral.integral_finsetSum (s := R)
    (f := fun n y => A x * B y * ((w n : ℂ) * ch (y - x) n))
    (fun n _ => (by
      have h1 : Continuous fun y : ℝ => A x * B y * ((w n : ℂ) * ch (y - x) n) :=
        (continuous_const.mul hBc).mul (continuous_const.mul
          ((hchc n).comp (by fun_prop : Continuous fun y : ℝ => y - x)))
      exact h1.intervalIntegrable _ _))]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [show (∑ n ∈ R, A x * B y * ((w n : ℂ) * ch (y - x) n))
      = A x * B y * W (y - x) from by
    rw [hW (y - x), Finset.mul_sum]]


/- NOTE: the instantiation of `weighted_sum_double` at `A = fhat S f * fhat S g`,
`B = conj (fhat S f * fhat S g)` and `ch θ n = exp (2πi θ n)` — i.e. the master identity
`∑ n, w n * (conv S f g n)^2 = ∬ fhat(x) conj fhat(y) W(y-x)` — is NOT proved here. Its first
`calc` step runs a defeq check on the literal `fhat` terms that exceeds 1,000,000 heartbeats;
the fix is the same `set` abbreviation that unblocked `inversion` (state `A`, `B`, `ch` locally
so the terms stay small), not a bigger heartbeat budget. -/



/-! ### 10. Periodicity of `fhat` -/

theorem exp_two_pi_I_int (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
  rw [show 2 * Real.pi * Complex.I * (n : ℂ) = (n : ℂ) * (2 * Real.pi * Complex.I) from by ring,
    Complex.exp_int_mul_two_pi_mul_I]

/-- `fhat` is `1`-periodic. -/
theorem fhat_add_one (S : Finset ℤ) (g : ℤ → ℝ) (α : ℝ) :
    fhat S g (α + 1) = fhat S g α := by
  rw [fhat_eq_sum', fhat_eq_sum']
  refine Finset.sum_congr rfl fun n _ => ?_
  have h : 2 * Real.pi * Complex.I * ((α + 1 : ℝ) : ℂ) * (n : ℂ)
      = 2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ) + 2 * Real.pi * Complex.I * (n : ℂ) := by
    push_cast; ring
  rw [h, Complex.exp_add, exp_two_pi_I_int, mul_one]

/-- `‖fhat S g‖²` is `1`-periodic. -/
theorem fhat_normsq_periodic (S : Finset ℤ) (g : ℤ → ℝ) :
    Function.Periodic (fun y : ℝ => ‖fhat S g y‖ ^ 2) 1 := by
  intro y
  simp only [fhat_add_one]

/-! ### 11. Local control of the integral, chained -/

/-- A function whose integral over every interval of length `2/H` is at most `Δ` has integral at
most `k·Δ` over every interval of length at most `k·(2/H)`. -/
theorem local_chain {Q : ℝ → ℝ} {H Δ : ℝ} (hH : 0 < H) (hΔ : 0 ≤ Δ)
    (hQc : Continuous Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQ : ∀ a : ℝ, (∫ x in a..(a + 2/H), Q x) ≤ Δ) :
    ∀ (k : ℕ) (a b : ℝ), a ≤ b → b - a ≤ (k:ℝ) * (2/H) → (∫ x in a..b, Q x) ≤ (k:ℝ) * Δ := by
  intro k
  induction k with
  | zero =>
    intro a b hab hlen
    have hba : b = a := by
      have h2 : (0:ℝ) < 2/H := by positivity
      nlinarith
    subst hba
    simp
  | succ k ih =>
    intro a b hab hlen
    have hpos : (0:ℝ) < 2/H := by positivity
    have hsucc : (↑(k+1) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [hsucc] at hlen ⊢
    by_cases hbc : b ≤ a + 2/H
    · have hmono : (∫ x in a..b, Q x) ≤ ∫ x in a..(a + 2/H), Q x :=
        intervalIntegral.integral_mono_interval le_rfl hab hbc
          (Filter.Eventually.of_forall hQ0) (hQc.intervalIntegrable _ _)
      have h1 : (∫ x in a..(a + 2/H), Q x) ≤ Δ := hQ a
      have hk1 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      nlinarith [hmono, h1, hΔ, hk1]
    · push_neg at hbc
      have hsplit : (∫ x in a..(a + 2/H), Q x) + (∫ x in (a + 2/H)..b, Q x)
          = ∫ x in a..b, Q x :=
        intervalIntegral.integral_add_adjacent_intervals
          (hQc.intervalIntegrable _ _) (hQc.intervalIntegrable _ _)
      have htail : (∫ x in (a + 2/H)..b, Q x) ≤ (k:ℝ) * Δ := by
        refine ih (a + 2/H) b (by linarith) ?_
        nlinarith [hlen]
      have hhead : (∫ x in a..(a + 2/H), Q x) ≤ Δ := hQ a
      rw [← hsplit]
      nlinarith [htail, hhead]

/-- The interval bound: `∫_a^b Q ≤ ((b-a)·H/2 + 1)·Δ`. -/
theorem interval_bound {Q : ℝ → ℝ} {H Δ : ℝ} (hH : 0 < H) (hΔ : 0 ≤ Δ)
    (hQc : Continuous Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQ : ∀ a : ℝ, (∫ x in a..(a + 2/H), Q x) ≤ Δ)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, Q x) ≤ ((b - a) * H / 2 + 1) * Δ := by
  set k : ℕ := Nat.ceil ((b - a) * H / 2) with hkdef
  have hk1 : (b - a) * H / 2 ≤ (k : ℝ) := Nat.le_ceil _
  have hk2 : (k : ℝ) < (b - a) * H / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlen : b - a ≤ (k : ℝ) * (2/H) := by
    have heq : (2/H) * ((b - a) * H / 2) = b - a := by
      field_simp
    have h2 : (2/H) * ((b - a) * H / 2) ≤ (2/H) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk1 (by positivity)
    linarith [heq, h2]
  have hmain := local_chain hH hΔ hQc hQ0 hQ k a b hab hlen
  have : (k : ℝ) * Δ ≤ ((b - a) * H / 2 + 1) * Δ :=
    mul_le_mul_of_nonneg_right (le_of_lt hk2) hΔ
  linarith [hmain]

/-! ### 12. The geometric piece bound -/

/-- On a short piece `[a,b]` with `0 < a ≤ b ≤ 2a` and `b ≤ 1/2` the kernel is bounded by
`1/(2Ma²)`, and the local control of `g` bounds its integral there. -/
theorem piece_bound {g : ℝ → ℝ} {W : ℝ → ℂ} {M : ℕ} {H Δ : ℝ}
    (hH : 0 < H) (hΔ : 0 ≤ Δ) (hM : (0:ℝ) < (M:ℝ))
    (hgc : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hg : ∀ a : ℝ, (∫ x in a..(a + 2/H), g x) ≤ Δ)
    (hWc : Continuous W)
    (hWdec : ∀ θ : ℝ, 0 < |θ| → |θ| ≤ 1/2 → ‖W θ‖ * (2 * (M:ℝ)) * θ ^ 2 ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2 * a) (hb2 : b ≤ 1/2) :
    (∫ u in a..b, g u * ‖W u‖) ≤ (1 / (2 * (M:ℝ) * a ^ 2)) * (((b - a) * H / 2 + 1) * Δ) := by
  have hM2 : (0:ℝ) < 2 * (M:ℝ) := by positivity
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have hC : (0:ℝ) ≤ 1 / (2 * (M:ℝ) * a ^ 2) := by positivity
  have hpt : ∀ u ∈ Set.Icc a b, g u * ‖W u‖ ≤ (1 / (2 * (M:ℝ) * a ^ 2)) * g u := by
    intro u hu
    have hau : a ≤ u := hu.1
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    have hu1 : |u| ≤ 1/2 := by
      rw [abs_of_pos hu0]
      exact le_trans hu.2 hb2
    have hpou : 0 < |u| := by rwa [abs_of_pos hu0]
    have hdec := hWdec u hpou hu1
    have hu2 : a ^ 2 ≤ u ^ 2 := by nlinarith
    have hWa : ‖W u‖ ≤ 1 / (2 * (M:ℝ) * a ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hstep : ‖W u‖ * (2 * (M:ℝ) * a ^ 2) ≤ ‖W u‖ * (2 * (M:ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (norm_nonneg _)
      calc ‖W u‖ * (2 * (M:ℝ) * a ^ 2) ≤ ‖W u‖ * (2 * (M:ℝ) * u ^ 2) := hstep
        _ = ‖W u‖ * (2 * (M:ℝ)) * u ^ 2 := by ring
        _ ≤ 1 := hdec
    have hgn : (0:ℝ) ≤ g u := hg0 u
    calc g u * ‖W u‖ ≤ g u * (1 / (2 * (M:ℝ) * a ^ 2)) := by
          refine mul_le_mul_of_nonneg_left hWa hgn
      _ = (1 / (2 * (M:ℝ) * a ^ 2)) * g u := by ring
  have hint1 : IntervalIntegrable (fun u => g u * ‖W u‖) volume a b :=
    (hgc.mul hWc.norm).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u => (1 / (2 * (M:ℝ) * a ^ 2)) * g u) volume a b :=
    (continuous_const.mul hgc).intervalIntegrable _ _
  have hmono : (∫ u in a..b, g u * ‖W u‖) ≤ ∫ u in a..b, (1 / (2 * (M:ℝ) * a ^ 2)) * g u :=
    intervalIntegral.integral_mono_on hab hint1 hint2 hpt
  have h2 : (∫ u in a..b, (1 / (2 * (M:ℝ) * a ^ 2)) * g u)
      = (1 / (2 * (M:ℝ) * a ^ 2)) * ∫ u in a..b, g u :=
    intervalIntegral.integral_const_mul _ _
  have h3 : (∫ u in a..b, g u) ≤ ((b - a) * H / 2 + 1) * Δ :=
    interval_bound hH hΔ hgc hg0 hg hab
  rw [h2] at hmono
  calc (∫ u in a..b, g u * ‖W u‖) ≤ (1 / (2 * (M:ℝ) * a ^ 2)) * ∫ u in a..b, g u := hmono
    _ ≤ (1 / (2 * (M:ℝ) * a ^ 2)) * (((b - a) * H / 2 + 1) * Δ) :=
        mul_le_mul_of_nonneg_left h3 hC

/-! ### 13. The telescoping ladder -/

/-- Telescoping decomposition of `∫_{-s K}^{s K} f` into the central piece and the geometric side
pieces. -/
theorem ladder_sum {f : ℝ → ℝ} (hf : Continuous f) {s : ℕ → ℝ} (hmono : Monotone s)
    (K : ℕ) :
    (∫ x in (-(s K))..(s K), f x)
      = (∫ x in (-(s 0))..(s 0), f x)
        + ∑ j ∈ Finset.range K,
            ((∫ x in (s j)..(s (j+1)), f x) + ∫ x in (-(s (j+1)))..(-(s j)), f x) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hle : s K ≤ s (K + 1) := hmono (Nat.le_succ K)
    have h1 : (∫ x in (-(s (K+1)))..(-(s K)), f x) + (∫ x in (-(s K))..(s K), f x)
        = ∫ x in (-(s (K+1)))..(s K), f x :=
      intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    have h2 : (∫ x in (-(s (K+1)))..(s K), f x) + (∫ x in (s K)..(s (K+1)), f x)
        = ∫ x in (-(s (K+1)))..(s (K+1)), f x :=
      intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    rw [Finset.sum_range_succ]
    linarith [h1, h2, ih]

/-! ### 14. The weighted kernel estimate -/

theorem geom_half_sum (n : ℕ) : (∑ j ∈ Finset.range n, ((1/2:ℝ))^j) ≤ 2 := by
  have h := geom_sum_eq (x := (1/2:ℝ)) (by norm_num) n
  rw [h]
  have h2 : ((1/2:ℝ)^n - 1)/(1/2-1) = 2 - 2*(1/2)^n := by
    field_simp
    ring
  rw [h2]
  have := pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n
  linarith

theorem two_pow_ge_succ : ∀ n : ℕ, (n:ℝ) + 1 ≤ (2:ℝ)^n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hstep : (2:ℝ)^(n+1) = 2*2^n := by rw [pow_succ]; ring
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    rw [hstep]; push_cast; linarith

/-- **The weighted second-moment kernel estimate.** If `Q`'s integral over every interval of
length `2/H` is at most `Δ`, and `W` is a `1`-periodic kernel with `|W| ≤ 2M` and
`|W(θ)| ≤ 1/(2Mθ²)` for `0 < |θ| ≤ 1/2`, then every shift of `W` against `Q` costs at most
`40·H·Δ`. -/
theorem kernel_estimate {Q : ℝ → ℝ} {W : ℝ → ℂ} {M : ℕ} {H Δ : ℝ}
    (hH : 2 ≤ H) (hΔ : 0 ≤ Δ) (hMge : 2*H ≤ (M:ℝ)) (hMle : (M:ℝ) ≤ 2*H + 5)
    (hQc : Continuous Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQper : Function.Periodic Q 1)
    (hQ : ∀ a : ℝ, (∫ x in a..(a + 2/H), Q x) ≤ Δ)
    (hWc : Continuous W) (hWper : ∀ θ : ℝ, W (θ + 1) = W θ)
    (hWnorm : ∀ θ : ℝ, ‖W θ‖ ≤ 2 * (M:ℝ))
    (hWdec : ∀ θ : ℝ, 0 < |θ| → |θ| ≤ 1/2 → ‖W θ‖ * (2 * (M:ℝ)) * θ ^ 2 ≤ 1)
    (c : ℝ) :
    (∫ y in (0:ℝ)..1, Q y * ‖W (y - c)‖) ≤ 40 * H * Δ := by
  have hH0 : (0:ℝ) < H := by linarith
  have hM0 : (0:ℝ) < (M:ℝ) := by linarith
  have hQc' : Continuous fun u : ℝ => Q (u + c) := hQc.comp (by fun_prop)
  -- (1) the periodic shift and the substitution
  have hper1 : Function.Periodic (fun y : ℝ => Q y * ‖W (y - c)‖) 1 := by
    intro y
    show Q (y + 1) * ‖W (y + 1 - c)‖ = Q y * ‖W (y - c)‖
    rw [hQper y, show y + 1 - c = (y - c) + 1 from by ring, hWper]
  have hshift : (∫ y in (0:ℝ)..1, Q y * ‖W (y - c)‖)
      = ∫ y in (c - 1/2)..(c + 1/2), Q y * ‖W (y - c)‖ := by
    have h := hper1.intervalIntegral_add_eq (0:ℝ) (c - 1/2)
    rw [show c - 1/2 + 1 = c + 1/2 from by ring] at h
    simpa using h
  have hsub : (∫ y in (c - 1/2)..(c + 1/2), Q y * ‖W (y - c)‖)
      = ∫ u in (-(1/2):ℝ)..(1/2), Q (u + c) * ‖W u‖ := by
    have h := intervalIntegral.integral_comp_add_right
      (f := fun y : ℝ => Q y * ‖W (y - c)‖) (a := (-(1/2):ℝ)) (b := (1/2:ℝ)) c
    rw [show (c - 1/2 : ℝ) = -(1/2) + c from by ring,
      show (c + 1/2 : ℝ) = 1/2 + c from by ring]
    rw [← h]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [add_sub_cancel_right]
  rw [hshift, hsub]
  -- (2) the middle piece
  have hmidQ : (∫ u in (-(1/H))..(1/H), Q (u + c)) ≤ Δ := by
    have h := intervalIntegral.integral_comp_add_right (f := Q) (a := (-(1/H):ℝ)) (b := (1/H:ℝ)) c
    rw [show -(1/H) + c = c - 1/H from by ring,
      show 1/H + c = c - 1/H + 2/H from by field_simp; ring] at h
    rw [h]
    exact hQ (c - 1/H)
  have hmid : (∫ u in (-(1/H))..(1/H), Q (u + c) * ‖W u‖) ≤ 2*(M:ℝ)*Δ := by
    have hpt : ∀ u ∈ Set.Icc (-(1/H)) (1/H), Q (u + c) * ‖W u‖ ≤ 2*(M:ℝ) * Q (u + c) := by
      intro u _
      have h1 : Q (u + c) * ‖W u‖ ≤ Q (u + c) * (2*(M:ℝ)) :=
        mul_le_mul_of_nonneg_left (hWnorm u) (hQ0 _)
      linarith [h1]
    have hi1 : IntervalIntegrable (fun u : ℝ => Q (u + c) * ‖W u‖) volume (-(1/H)) (1/H) :=
      ((hQc'.mul hWc.norm)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => 2*(M:ℝ) * Q (u + c)) volume (-(1/H)) (1/H) :=
      (continuous_const.mul hQc').intervalIntegrable _ _
    have hle : (-(1/H):ℝ) ≤ 1/H := by
      have : (0:ℝ) < 1/H := by positivity
      linarith
    have hmono := intervalIntegral.integral_mono_on hle hi1 hi2 hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    have h2 := mul_le_mul_of_nonneg_left hmidQ (by positivity : (0:ℝ) ≤ 2*(M:ℝ))
    linarith [hmono, h2]
  -- (3) the ladder of side pieces
  set s : ℕ → ℝ := fun j => min ((2:ℝ)^j / H) (1/2) with hsdef
  have hs_nn : ∀ j, 0 < s j := by
    intro j
    show (0:ℝ) < min ((2:ℝ)^j / H) (1/2)
    exact lt_min (by positivity) (by norm_num)
  have hs_mono : Monotone s := by
    intro i j hij
    show min ((2:ℝ)^i / H) (1/2) ≤ min ((2:ℝ)^j / H) (1/2)
    have h2 : (2:ℝ)^i ≤ (2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hij
    exact min_le_min (by gcongr) le_rfl
  have hs_geo : ∀ j, s (j+1) ≤ 2 * s j := by
    intro j
    have hpow : (2:ℝ)^(j+1) = 2 * (2:ℝ)^j := by rw [pow_succ]; ring
    show min ((2:ℝ)^(j+1) / H) (1/2) ≤ 2 * min ((2:ℝ)^j / H) (1/2)
    rw [hpow]
    rcases le_total ((2:ℝ)^j / H) (1/2) with h | h
    · rw [min_eq_left h]
      refine le_trans (min_le_left (2 * (2:ℝ)^j / H) (1/2)) (le_of_eq ?_)
      ring
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = Nat.ceil H + 2 := ⟨_, rfl⟩
  have hKbig : (H/2) ≤ (2:ℝ)^K := by
    have h1 : (K:ℝ) + 1 ≤ (2:ℝ)^K := two_pow_ge_succ K
    have h2 : (Nat.ceil H : ℝ) < H + 1 := Nat.ceil_lt_add_one (by linarith)
    have h4 : H ≤ (Nat.ceil H : ℝ) := Nat.le_ceil H
    have h3 : (K:ℝ) = (Nat.ceil H : ℝ) + 2 := by rw [hKdef]; push_cast; ring
    linarith
  have hKle : (K:ℝ) ≤ H + 3 := by
    have h2 : (Nat.ceil H : ℝ) < H + 1 := Nat.ceil_lt_add_one (by linarith)
    have h3 : (K:ℝ) = (Nat.ceil H : ℝ) + 2 := by rw [hKdef]; push_cast; ring
    linarith
  have hs0 : s 0 = 1/H := by
    have h2 : ((2:ℝ)^0 / H) = 1/H := by norm_num
    have hle : (1:ℝ)/H ≤ 1/2 := by
      rw [div_le_iff₀ hH0]; linarith
    show min ((2:ℝ)^0 / H) (1/2) = 1/H
    rw [h2, min_eq_left hle]
  have hsK : s K = 1/2 := by
    have hle : (1:ℝ)/2 ≤ (2:ℝ)^K / H := by
      rw [le_div_iff₀ hH0]; linarith
    show min ((2:ℝ)^K / H) (1/2) = 1/2
    exact min_eq_right hle
  have hlad := ladder_sum (f := fun u : ℝ => Q (u + c) * ‖W u‖)
    (hQc'.mul hWc.norm) hs_mono K
  rw [hsK, hs0] at hlad
  -- (4) bounds for the pieces
  have hpiece : ∀ j ∈ Finset.range K,
      (∫ u in (s j)..(s (j+1)), Q (u + c) * ‖W u‖)
        + (∫ u in (-(s (j+1)))..(-(s j)), Q (u + c) * ‖W u‖)
      ≤ (H/(2*(M:ℝ)*(s j)) + 1/((M:ℝ)*(s j)^2)) * Δ := by
    intro j _
    have hsj : 0 < s j := hs_nn j
    have hle1 : s j ≤ s (j+1) := hs_mono (Nat.le_succ j)
    have hle2 : s (j+1) ≤ 2 * s j := hs_geo j
    have hle3 : s (j+1) ≤ 1/2 := by
      show min ((2:ℝ)^(j+1) / H) (1/2) ≤ 1/2
      exact min_le_right _ _
    have hQshift : ∀ a : ℝ, (∫ x in a..(a + 2/H), Q (x + c)) ≤ Δ := by
      intro a
      have h := intervalIntegral.integral_comp_add_right (f := Q) (a := a) (b := a + 2/H) c
      rw [h, show a + 2/H + c = (a + c) + 2/H from by ring]
      exact hQ (a + c)
    have hpos : (∫ u in (s j)..(s (j+1)), Q (u + c) * ‖W u‖)
        ≤ (1 / (2 * (M:ℝ) * (s j) ^ 2)) * (((s (j+1) - s j) * H / 2 + 1) * Δ) :=
      piece_bound hH0 hΔ hM0 hQc' (fun x => hQ0 _) hQshift hWc hWdec hsj hle1 hle2 hle3
    have hnegshift : (∫ u in (-(s (j+1)))..(-(s j)), Q (u + c) * ‖W u‖)
        = ∫ u in (s j)..(s (j+1)), Q (c - u) * ‖W (-u)‖ := by
      have h := intervalIntegral.integral_comp_neg
        (f := fun u : ℝ => Q (u + c) * ‖W u‖) (a := (s j)) (b := (s (j+1)))
      rw [h.symm]
      refine intervalIntegral.integral_congr fun x _ => ?_
      show Q (-x + c) * ‖W (-x)‖ = Q (c - x) * ‖W (-x)‖
      rw [show -x + c = c - x from by ring]
    have hQneg : ∀ a : ℝ, (∫ x in a..(a + 2/H), Q (c - x)) ≤ Δ := by
      intro a
      have hA : (∫ x in a..(a + 2/H), Q (c - x))
          = ∫ y in (-(a + 2/H))..(-a), Q (c + y) := by
        have h := intervalIntegral.integral_comp_neg
          (f := fun u : ℝ => Q (c + u)) (a := a) (b := a + 2/H)
        simpa only [sub_eq_add_neg] using h
      have hB : (∫ y in (-(a + 2/H))..(-a), Q (c + y))
          = ∫ u in (c - a - 2/H)..(c - a), Q u := by
        have h := intervalIntegral.integral_comp_add_right
          (f := Q) (a := (-(a + 2/H))) (b := (-a)) c
        rw [show -(a + 2/H) + c = c - a - 2/H from by ring,
          show -a + c = c - a from by ring] at h
        simpa only [add_comm] using h
      rw [hA, hB]
      have h3 := hQ (c - a - 2/H)
      rwa [show c - a - 2/H + 2/H = c - a from by ring] at h3
    have hneg : (∫ u in (s j)..(s (j+1)), Q (c - u) * ‖W (-u)‖)
        ≤ (1 / (2 * (M:ℝ) * (s j) ^ 2)) * (((s (j+1) - s j) * H / 2 + 1) * Δ) := by
      refine piece_bound (W := fun u => W (-u)) hH0 hΔ hM0
        (hQc.comp (by fun_prop : Continuous fun u : ℝ => c - u)) (fun u => hQ0 _) hQneg
        (hWc.comp (by fun_prop : Continuous fun u : ℝ => -u)) ?_ hsj hle1 hle2 hle3
      intro θ hθ hθ2
      have h1 := hWdec (-θ) (by rwa [abs_neg]) (by rwa [abs_neg])
      rwa [neg_sq] at h1
    rw [hnegshift]
    have hcom : 2 * ((1 / (2 * (M:ℝ) * (s j) ^ 2)) * (((s (j+1) - s j) * H / 2 + 1) * Δ))
        ≤ (H/(2*(M:ℝ)*(s j)) + 1/((M:ℝ)*(s j)^2)) * Δ := by
      have hle : s (j+1) - s j ≤ s j := by linarith
      have h1 : ((s (j+1) - s j) * H / 2 + 1) ≤ (s j * H / 2 + 1) := by nlinarith
      have h2 : 2 * ((1 / (2 * (M:ℝ) * (s j) ^ 2)) * (((s (j+1) - s j) * H / 2 + 1) * Δ))
          ≤ 2 * ((1 / (2 * (M:ℝ) * (s j) ^ 2)) * ((s j * H / 2 + 1) * Δ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right h1 hΔ
      have h3 : 2 * ((1 / (2 * (M:ℝ) * (s j) ^ 2)) * ((s j * H / 2 + 1) * Δ))
          = (H/(2*(M:ℝ)*(s j)) + 1/((M:ℝ)*(s j)^2)) * Δ := by
        have hsj' : (s j) ≠ 0 := (hs_nn j).ne'
        have hMs : (M:ℝ) ≠ 0 := hM0.ne'
        field_simp
        try ring
      linarith [h2, h3]
    linarith [hpos, hneg, hcom]
  -- (5) sum of the piece bounds
  have hsum1 : (∑ j ∈ Finset.range K,
      ((∫ u in (s j)..(s (j+1)), Q (u + c) * ‖W u‖)
        + ∫ u in (-(s (j+1)))..(-(s j)), Q (u + c) * ‖W u‖))
      ≤ ∑ j ∈ Finset.range K, ((H/(2*(M:ℝ)*(s j)) + 1/((M:ℝ)*(s j)^2)) * Δ) :=
    Finset.sum_le_sum hpiece
  have hsinv : ∀ j, (1:ℝ)/(s j) ≤ H/(2:ℝ)^j + 2 := by
    intro j
    have h2j : (0:ℝ) < (2:ℝ)^j := by positivity
    rcases le_total ((2:ℝ)^j / H) (1/2) with h | h
    · have hs : s j = (2:ℝ)^j / H := by
        show min ((2:ℝ)^j / H) (1/2) = _
        exact min_eq_left h
      rw [hs, one_div, inv_div]
      linarith
    · have hs : s j = 1/2 := by
        show min ((2:ℝ)^j / H) (1/2) = _
        exact min_eq_right h
      rw [hs]
      have : (0:ℝ) ≤ H/(2:ℝ)^j := by positivity
      norm_num
      linarith
  have hS1 : (∑ j ∈ Finset.range K, (1:ℝ)/(s j)) ≤ 10*H := by
    have hb : (∑ j ∈ Finset.range K, (1:ℝ)/(s j))
        ≤ ∑ j ∈ Finset.range K, (H/(2:ℝ)^j + 2) := Finset.sum_le_sum (fun j _ => hsinv j)
    have h2 : ∀ j : ℕ, H/(2:ℝ)^j = H * ((1/2:ℝ))^j := by
      intro j
      have hh : ((2:ℝ)^j)⁻¹ = ((1/2:ℝ))^j := by
        rw [show (1/2:ℝ) = (2:ℝ)⁻¹ from by norm_num, inv_pow]
      rw [div_eq_mul_inv, hh]
    have hsplit : (∑ j ∈ Finset.range K, (H/(2:ℝ)^j + 2))
        = H * (∑ j ∈ Finset.range K, ((1/2:ℝ))^j) + 2 * (K:ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range]
      simp only [h2]
      ring
    have hg := geom_half_sum K
    have hg0 : (0:ℝ) ≤ ∑ j ∈ Finset.range K, ((1/2:ℝ))^j :=
      Finset.sum_nonneg (fun j _ => by positivity)
    have h1 : H * (∑ j ∈ Finset.range K, ((1/2:ℝ))^j) ≤ H * 2 :=
      mul_le_mul_of_nonneg_left hg (by linarith)
    rw [hsplit] at hb
    nlinarith [hb, h1, hKle, hH]
  have hS2 : (∑ j ∈ Finset.range K, (1:ℝ)/(s j)^2) ≤ 10*H*(H+2) := by
    have hb : (∑ j ∈ Finset.range K, (1:ℝ)/(s j)^2)
        ≤ ∑ j ∈ Finset.range K, ((H+2) * (1/(s j))) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hsj : 0 < s j := hs_nn j
      have h1 : (1:ℝ)/(s j) ≤ H + 2 := by
        have h3 := hsinv j
        have h4 : H/(2:ℝ)^j ≤ H := by
          have h5 : (1:ℝ) ≤ (2:ℝ)^j := by
            have h6 := two_pow_ge_succ j
            have h7 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
            linarith
          have h8 : (0:ℝ) < (2:ℝ)^j := by positivity
          rw [div_le_iff₀ h8]
          nlinarith [hH]
        linarith
      have h2 : (1:ℝ)/(s j)^2 = (1/(s j)) * (1/(s j)) := by ring
      rw [h2]
      have h3 : (0:ℝ) ≤ 1/(s j) := by positivity
      nlinarith [h1, h3]
    have hstep : (∑ j ∈ Finset.range K, ((H+2) * (1/(s j))))
        = (H+2) * ∑ j ∈ Finset.range K, (1:ℝ)/(s j) := by
      rw [Finset.mul_sum]
    have hH2 : (0:ℝ) ≤ H + 2 := by linarith
    have h1 : (H+2) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j)) ≤ (H+2) * (10*H) :=
      mul_le_mul_of_nonneg_left hS1 hH2
    rw [hstep] at hb
    nlinarith [hb, h1]
  -- (6) assemble
  have hcoefA : (∑ j ∈ Finset.range K, H/(2*(M:ℝ)*(s j)))
      = (H/(2*(M:ℝ))) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsj' : (s j) ≠ 0 := (hs_nn j).ne'
    have hMs : (M:ℝ) ≠ 0 := hM0.ne'
    field_simp
    try ring
  have hcoefB : (∑ j ∈ Finset.range K, 1/((M:ℝ)*(s j)^2))
      = (1/(M:ℝ)) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j)^2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsj' : (s j) ≠ 0 := (hs_nn j).ne'
    have hMs : (M:ℝ) ≠ 0 := hM0.ne'
    field_simp
    try ring
  have hcoef : (∑ j ∈ Finset.range K, ((H/(2*(M:ℝ)*(s j)) + 1/((M:ℝ)*(s j)^2)) * Δ))
      = ((H/(2*(M:ℝ))) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j))
          + (1/(M:ℝ)) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j)^2)) * Δ := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hcoefA, hcoefB]
  have hbig : ((H/(2*(M:ℝ))) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j))
      + (1/(M:ℝ)) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j)^2)) ≤ 20*H := by
    have h1 : H/(2*(M:ℝ)) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j)) ≤ H/(2*(M:ℝ)) * (10*H) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have h2 : (1/(M:ℝ)) * (∑ j ∈ Finset.range K, (1:ℝ)/(s j)^2) ≤ (1/(M:ℝ)) * (10*H*(H+2)) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h3 : H/(2*(M:ℝ)) * (10*H) = 5*H^2/(M:ℝ) := by field_simp; try ring
    have h4 : (1/(M:ℝ)) * (10*H*(H+2)) = 10*H*(H+2)/(M:ℝ) := by field_simp; try ring
    have h5 : 5*H^2/(M:ℝ) ≤ 5*H^2/(2*H) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hMge
    have h6 : 10*H*(H+2)/(M:ℝ) ≤ 10*H*(H+2)/(2*H) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hMge
    have h7 : 5*H^2/(2*H) = 5*H/2 := by field_simp; try ring
    have h8 : 10*H*(H+2)/(2*H) = 5*(H+2) := by field_simp; try ring
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  rw [hlad]
  have hsum2 : (∑ j ∈ Finset.range K,
      ((H/(2*(M:ℝ)*(s j)) + 1/((M:ℝ)*(s j)^2)) * Δ)) ≤ 20*H*Δ := by
    rw [hcoef]
    exact mul_le_mul_of_nonneg_right hbig hΔ
  have hmid10 : 2*(M:ℝ)*Δ ≤ 10*H*Δ := by
    have : 2*(M:ℝ) ≤ 10*H := by linarith
    exact mul_le_mul_of_nonneg_right this hΔ
  have hHΔ : (0:ℝ) ≤ H * Δ := mul_nonneg (by linarith) hΔ
  linarith [hmid, hsum1, hsum2, hmid10, hHΔ]

/-- The same estimate for `1 ≤ H`; for `H < 2` the crude `|W| ≤ 2M` bound suffices. -/
theorem kernel_estimate' {Q : ℝ → ℝ} {W : ℝ → ℂ} {M : ℕ} {H Δ : ℝ}
    (hH : 1 ≤ H) (hΔ : 0 ≤ Δ) (hMge : 2*H ≤ (M:ℝ)) (hMle : (M:ℝ) ≤ 2*H + 5)
    (hQc : Continuous Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQper : Function.Periodic Q 1)
    (hQ : ∀ a : ℝ, (∫ x in a..(a + 2/H), Q x) ≤ Δ)
    (hWc : Continuous W) (hWper : ∀ θ : ℝ, W (θ + 1) = W θ)
    (hWnorm : ∀ θ : ℝ, ‖W θ‖ ≤ 2 * (M:ℝ))
    (hWdec : ∀ θ : ℝ, 0 < |θ| → |θ| ≤ 1/2 → ‖W θ‖ * (2 * (M:ℝ)) * θ ^ 2 ≤ 1)
    (c : ℝ) :
    (∫ y in (0:ℝ)..1, Q y * ‖W (y - c)‖) ≤ 40 * H * Δ := by
  by_cases h2 : 2 ≤ H
  · exact kernel_estimate h2 hΔ hMge hMle hQc hQ0 hQper hQ hWc hWper hWnorm hWdec c
  push_neg at h2
  have hH0 : (0:ℝ) < H := by linarith
  have hM0 : (0:ℝ) < (M:ℝ) := by linarith
  -- move the shift to the centred window
  have hper1 : Function.Periodic (fun y : ℝ => Q y * ‖W (y - c)‖) 1 := by
    intro y
    show Q (y + 1) * ‖W (y + 1 - c)‖ = Q y * ‖W (y - c)‖
    rw [hQper y, show y + 1 - c = (y - c) + 1 from by ring, hWper]
  have hshift : (∫ y in (0:ℝ)..1, Q y * ‖W (y - c)‖)
      = ∫ y in (c - 1/2)..(c + 1/2), Q y * ‖W (y - c)‖ := by
    have h := hper1.intervalIntegral_add_eq (0:ℝ) (c - 1/2)
    rw [show c - 1/2 + 1 = c + 1/2 from by ring] at h
    simpa using h
  have hsub : (∫ y in (c - 1/2)..(c + 1/2), Q y * ‖W (y - c)‖)
      = ∫ u in (-(1/2):ℝ)..(1/2), Q (u + c) * ‖W u‖ := by
    have h := intervalIntegral.integral_comp_add_right
      (f := fun y : ℝ => Q y * ‖W (y - c)‖) (a := (-(1/2):ℝ)) (b := (1/2:ℝ)) c
    rw [show (c - 1/2 : ℝ) = -(1/2) + c from by ring,
      show (c + 1/2 : ℝ) = 1/2 + c from by ring]
    rw [← h]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [add_sub_cancel_right]
  rw [hshift, hsub]
  -- the window has length `1`
  have hQmid : (∫ u in (-(1/2):ℝ)..(1/2), Q (u + c)) ≤ (H / 2 + 1) * Δ := by
    have h := intervalIntegral.integral_comp_add_right (f := Q) (a := (-(1/2):ℝ)) (b := (1/2:ℝ)) c
    rw [show -(1/2) + c = c - 1/2 from by ring,
      show (1/2 : ℝ) + c = c - 1/2 + 1 from by ring] at h
    rw [h]
    have hb := interval_bound hH0 hΔ hQc hQ0 hQ (show (c - 1/2 : ℝ) ≤ c - 1/2 + 1 by linarith)
    rw [show c - 1/2 + 1 - (c - 1/2) = 1 from by ring] at hb
    simpa using hb
  have hmono : (∫ u in (-(1/2):ℝ)..(1/2), Q (u + c) * ‖W u‖)
      ≤ 2*(M:ℝ) * ((H/2 + 1) * Δ) := by
    have hpt : ∀ u ∈ Set.Icc (-(1/2):ℝ) (1/2), Q (u + c) * ‖W u‖ ≤ 2*(M:ℝ) * Q (u + c) := by
      intro u _
      have h1 : Q (u + c) * ‖W u‖ ≤ Q (u + c) * (2*(M:ℝ)) :=
        mul_le_mul_of_nonneg_left (hWnorm u) (hQ0 _)
      linarith [h1]
    have hQc' : Continuous fun u : ℝ => Q (u + c) := hQc.comp (by fun_prop)
    have hi1 : IntervalIntegrable (fun u : ℝ => Q (u + c) * ‖W u‖) volume (-(1/2)) (1/2) :=
      (hQc'.mul hWc.norm).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => 2*(M:ℝ) * Q (u + c)) volume (-(1/2)) (1/2) :=
      (continuous_const.mul hQc').intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (show (-(1/2):ℝ) ≤ 1/2 by norm_num) hi1 hi2 hpt
    rw [intervalIntegral.integral_const_mul] at hm
    have h2' := mul_le_mul_of_nonneg_left hQmid (by positivity : (0:ℝ) ≤ 2*(M:ℝ))
    linarith [hm, h2']
  have hb1 : (2:ℝ)*(M:ℝ) ≤ 2*(2*H+5) := by linarith
  have hb2 : H/2 + 1 ≤ (3/2)*H := by linarith
  have hstep : 2*(M:ℝ) * ((H/2+1)*Δ) ≤ 40*H*Δ := by
    have h5 : (0:ℝ) ≤ H/2 + 1 := by linarith
    have h6 : (0:ℝ) ≤ 2*(M:ℝ) := by linarith
    have h7 : 2*(M:ℝ) * (H/2+1) ≤ 40*H := by nlinarith [hb1, hb2, h2, hH]
    nlinarith [h7, hΔ]
  linarith [hmono, hstep]

/-! ### 15. The tent kernel and the two bounds on its transform -/

local notation "𝕖" => fun (θ : ℝ) (n : ℤ) =>
  Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (n:ℂ))

/-- `max 0 (1 - |r|/M) = 1 - |r|/M` when `|r| < M`. -/
theorem tent_max_pos {M : ℕ} (hM : 1 ≤ M) {r : ℝ} (hr : |r| < (M:ℝ)) :
    max 0 (1 - |r| / (M:ℝ)) = 1 - |r| / (M:ℝ) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have h1 : |r| / (M:ℝ) < 1 := by
    rw [div_lt_one hM0]; exact hr
  exact max_eq_right (by linarith : (0:ℝ) ≤ 1 - |r|/(M:ℝ))

/-- The character is multiplicative in the index. -/
theorem char_mul (θ : ℝ) (m n : ℤ) : 𝕖 θ (m + n) = 𝕖 θ m * 𝕖 θ n := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `𝕖 θ j` is the `j`-th power of `𝕖 θ 1`. -/
theorem ech_one_pow (θ : ℝ) (j : ℕ) :
    𝕖 θ ((j:ℤ)) = (𝕖 θ 1) ^ j := by
  have h1 : 𝕖 θ 1 = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ)) := by
    push_cast
    rw [mul_one]
  rw [h1, exp_char_pow]
  push_cast
  rfl

/-- **The transform of the tent weight**, in the form the kernel bounds use. -/
theorem tent_kernel_eq {M : ℕ} (hM : 1 ≤ M) (x₀ : ℤ) (θ : ℝ) :
    (∑ n ∈ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)),
        (((2 * max 0 (1 - |((n:ℝ) - (x₀:ℝ))|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 θ n)
      = 𝕖 θ x₀ * ((2/(M:ℝ) : ℝ) : ℂ)
          * ((∑ j ∈ Finset.range M, (𝕖 θ 1) ^ j)
              * (∑ j ∈ Finset.range M, ((𝕖 θ 1) ^ j)⁻¹)) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hMm : ((M-1:ℕ):ℝ) = (M:ℝ) - 1 := by
    push_cast [Nat.cast_sub hM]; ring
  -- step 1: reindex the interval at `x₀`
  have hR : Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ))
      = (Finset.Icc (-(((M-1:ℕ)):ℤ)) (((M-1:ℕ)):ℤ)).image (fun k : ℤ => x₀ + k) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨n - x₀, ⟨by omega, by omega⟩, by ring⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      omega
  have hval : ∀ k : ℤ, |(k:ℝ)| ≤ ((M-1:ℕ):ℝ) →
      (max 0 (1 - |(((x₀ + k : ℤ):ℝ) - (x₀:ℝ))|/(M:ℝ))) = 1 - |(k:ℝ)|/(M:ℝ) := by
    intro k hk
    have h1 : ((x₀ + k : ℤ):ℝ) - (x₀:ℝ) = (k:ℝ) := by push_cast; ring
    rw [h1]
    have h2 : |(k:ℝ)| < (M:ℝ) := by rw [hMm] at hk; linarith
    exact tent_max_pos hM h2
  set G : ℤ → ℂ := fun k =>
    (((2 * max 0 (1 - |((x₀ + k : ℤ):ℝ) - (x₀:ℝ)|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 θ (x₀ + k) with hG
  have hGval : ∀ k : ℤ, |(k:ℝ)| ≤ ((M-1:ℕ):ℝ) →
      G k = ((2 * (1 - |(k:ℝ)|/(M:ℝ)) : ℝ) : ℂ) * 𝕖 θ (x₀ + k) := by
    intro k hk
    simp only [hG, hval k hk]
  have hstep : (∑ n ∈ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)),
        (((2 * max 0 (1 - |((n:ℝ) - (x₀:ℝ))|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 θ n)
      = ∑ k ∈ Finset.Icc (-(((M-1:ℕ)):ℤ)) (((M-1:ℕ)):ℤ), G k := by
    rw [hR, Finset.sum_image (by intro a _ b _ hab; exact add_left_cancel hab)]
  rw [hstep, icc_split_sum (M-1) G]
  -- step 3: the centre term
  have hzero : G 0 = 2 * 𝕖 θ x₀ := by
    rw [hGval 0 (by simp)]
    have h1 : |((0:ℤ):ℝ)| = 0 := by simp
    rw [h1, zero_div, sub_zero]
    norm_num
  -- step 4: the paired terms
  have hterm : ∀ i ∈ Finset.range (M-1),
      (G ((i:ℤ)+1) + G (-((i:ℤ)+1)))
        = ((2 * (1 - ((i:ℝ)+1)/(M:ℝ)) : ℝ) : ℂ)
            * (𝕖 θ (x₀ + ((i:ℤ)+1)) + 𝕖 θ (x₀ - ((i:ℤ)+1))) := by
    intro i hi
    have hi' : i < M - 1 := Finset.mem_range.mp hi
    have hsucc : ((i:ℤ)+1 : ℤ) = ((i+1:ℕ):ℤ) := by push_cast; ring
    have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
    have habs1 : |((((i:ℤ)+1 : ℤ)):ℝ)| = (i:ℝ)+1 := by
      rw [hsucc, abs_of_nonneg (by positivity)]
      exact hcast
    have habs2 : |(((-((i:ℤ)+1) : ℤ)):ℝ)| = (i:ℝ)+1 := by
      push_cast
      rw [abs_neg]
      exact abs_of_nonneg (show (0:ℝ) ≤ (i:ℝ)+1 from by positivity)
    have hnum : (i:ℝ)+1 ≤ ((M-1:ℕ):ℝ) := by
      have h1 : i + 1 ≤ M - 1 := Nat.succ_le_of_lt hi'
      have h2 : ((i+1:ℕ):ℝ) ≤ (((M-1:ℕ)):ℝ) := by exact_mod_cast h1
      rw [hcast] at h2
      exact h2
    have hle : |((((i:ℤ)+1 : ℤ)):ℝ)| ≤ ((M-1:ℕ):ℝ) := by rw [habs1]; exact hnum
    have hle2 : |(((-((i:ℤ)+1) : ℤ)):ℝ)| ≤ ((M-1:ℕ):ℝ) := by rw [habs2]; exact hnum
    rw [hGval ((i:ℤ)+1) hle, hGval (-((i:ℤ)+1)) hle2, habs1, habs2]
    simp only [sub_eq_add_neg]
    ring
  rw [hzero, Finset.sum_congr rfl hterm]
  rw [tent_transform x₀ M hM θ]
  -- identify the two geometric sums
  have hsum1 : ∀ j : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (j:ℂ)) = (𝕖 θ 1) ^ j := by
    intro j
    have h1 : 𝕖 θ 1 = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ)) := by
      push_cast
      rw [mul_one]
    rw [h1]
    exact (exp_char_pow θ j).symm
  simp only [hsum1]

theorem char_periodic (θ : ℝ) (n : ℤ) : 𝕖 (θ + 1) n = 𝕖 θ n := by
  show Complex.exp (2 * Real.pi * Complex.I * ((θ + 1 : ℝ):ℂ) * (n:ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (n:ℂ))
  have h : 2 * Real.pi * Complex.I * ((θ + 1 : ℝ):ℂ) * (n:ℂ)
      = 2 * Real.pi * Complex.I * (θ:ℂ) * (n:ℂ) + 2 * Real.pi * Complex.I * (n:ℂ) := by
    push_cast; ring
  rw [h, Complex.exp_add, exp_two_pi_I_int, mul_one]

/-- The tent kernel is `1`-periodic. -/
theorem tent_kernel_periodic {M : ℕ} (x₀ : ℤ) (θ : ℝ) :
    (∑ n ∈ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)),
        (((2 * max 0 (1 - |((n:ℝ) - (x₀:ℝ))|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 (θ + 1) n)
      = ∑ n ∈ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)),
        (((2 * max 0 (1 - |((n:ℝ) - (x₀:ℝ))|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 θ n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [char_periodic]

/-- The tent kernel is continuous in `θ`. -/
theorem tent_kernel_continuous (M : ℕ) (x₀ : ℤ) :
    Continuous fun θ : ℝ =>
      ∑ n ∈ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)),
        (((2 * max 0 (1 - |((n:ℝ) - (x₀:ℝ))|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 θ n :=
  continuous_finsetSum _ (fun n _ => continuous_const.mul (continuous_exp_char n))

/-- `|W| ≤ 2M` for the tent kernel. -/
theorem tent_kernel_norm_le {M : ℕ} (hM : 1 ≤ M) (x₀ : ℤ) (θ : ℝ) :
    ‖∑ n ∈ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)),
        (((2 * max 0 (1 - |((n:ℝ) - (x₀:ℝ))|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 θ n‖ ≤ 2*(M:ℝ) := by
  rw [tent_kernel_eq hM x₀ θ]
  exact W_norm_le (𝕖 θ x₀) (𝕖 θ 1) (norm_exp_char θ x₀) (norm_exp_char θ 1) M hM

/-- The decay bound `|W(θ)|·2M·θ² ≤ 1` for `0 < |θ| ≤ 1/2`. -/
theorem tent_kernel_decay_le {M : ℕ} (hM : 1 ≤ M) (x₀ : ℤ) {θ : ℝ}
    (hθ : 0 < |θ|) (hθ2 : |θ| ≤ 1/2) :
    ‖∑ n ∈ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)),
        (((2 * max 0 (1 - |((n:ℝ) - (x₀:ℝ))|/(M:ℝ))) : ℝ) : ℂ) * 𝕖 θ n‖
      * (2*(M:ℝ)) * θ^2 ≤ 1 := by
  rw [tent_kernel_eq hM x₀ θ]
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hech1 : 𝕖 θ 1 = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ)) := by
    push_cast
    rw [mul_one]
  have hsin : ‖1 - 𝕖 θ 1‖^2 = 4 * Real.sin (Real.pi * θ)^2 := by
    rw [hech1]
    exact norm_one_sub_exp θ
  have h1 := W_decay_le (𝕖 θ x₀) (𝕖 θ 1) (norm_exp_char θ x₀) (norm_exp_char θ 1) M hM θ hsin
  -- `sin²(πθ) ≥ 4θ²` on `|θ| ≤ 1/2`
  have hsin2 : 4 * θ^2 ≤ Real.sin (Real.pi * θ)^2 := by
    have hsq : (2 * |θ|)^2 ≤ Real.sin (Real.pi * |θ|)^2 := by
      have h2 := two_mul_le_sin_pi (le_of_lt hθ) hθ2
      have hnn : 0 ≤ Real.sin (Real.pi * |θ|) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
      nlinarith [h2, hnn]
    have heq : Real.sin (Real.pi * |θ|)^2 = Real.sin (Real.pi * θ)^2 := by
      by_cases h : 0 ≤ θ
      · rw [abs_of_nonneg h]
      · push_neg at h
        rw [abs_of_neg h, show Real.pi * -θ = -(Real.pi * θ) from by ring, Real.sin_neg]
        ring
    have h3 : (2 * |θ|)^2 = 4 * θ^2 := by rw [mul_pow, sq_abs]; ring
    rw [h3] at hsq
    rw [heq] at hsq
    exact hsq
  have hX : (0:ℝ) ≤ ‖𝕖 θ x₀ * ((2/(M:ℝ) : ℝ) : ℂ)
      * ((∑ j ∈ Finset.range M, (𝕖 θ 1) ^ j)
          * (∑ j ∈ Finset.range M, ((𝕖 θ 1) ^ j)⁻¹))‖ := norm_nonneg _
  have hstep1 : ‖𝕖 θ x₀ * ((2/(M:ℝ) : ℝ) : ℂ)
      * ((∑ j ∈ Finset.range M, (𝕖 θ 1) ^ j)
          * (∑ j ∈ Finset.range M, ((𝕖 θ 1) ^ j)⁻¹))‖ * (4 * θ^2) ≤ 2 / (M:ℝ) := by
    calc ‖𝕖 θ x₀ * ((2/(M:ℝ) : ℝ) : ℂ)
        * ((∑ j ∈ Finset.range M, (𝕖 θ 1) ^ j)
            * (∑ j ∈ Finset.range M, ((𝕖 θ 1) ^ j)⁻¹))‖ * (4 * θ^2)
        ≤ ‖𝕖 θ x₀ * ((2/(M:ℝ) : ℝ) : ℂ)
            * ((∑ j ∈ Finset.range M, (𝕖 θ 1) ^ j)
                * (∑ j ∈ Finset.range M, ((𝕖 θ 1) ^ j)⁻¹))‖ * Real.sin (Real.pi * θ)^2 :=
          mul_le_mul_of_nonneg_left hsin2 hX
      _ ≤ 2 / (M:ℝ) := h1
  have hstep2 : (‖𝕖 θ x₀ * ((2/(M:ℝ) : ℝ) : ℂ)
      * ((∑ j ∈ Finset.range M, (𝕖 θ 1) ^ j)
          * (∑ j ∈ Finset.range M, ((𝕖 θ 1) ^ j)⁻¹))‖ * (4 * θ^2)) * (M:ℝ)
        ≤ (2/(M:ℝ)) * (M:ℝ) :=
    mul_le_mul_of_nonneg_right hstep1 (le_of_lt hM0)
  have hdiv : (2/(M:ℝ)) * (M:ℝ) = 2 := by
    field_simp
  rw [hdiv] at hstep2
  nlinarith [hstep2]

/-! ### 16. The window lies in the weighted range, with weight at least one -/

theorem win_subset_R {X H : ℝ} (hH : 1 ≤ H) {M : ℕ} {x₀ : ℤ}
    (hx₀ : (⌊X⌋ : ℤ) = x₀) (hHM : H + 1 ≤ (M:ℝ)) :
    win X H ⊆ Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)) := by
  have hM2 : 1 ≤ M := by
    have : (1:ℝ) ≤ (M:ℝ) := by linarith
    exact_mod_cast this
  intro n hn
  simp only [win, Finset.mem_Icc] at hn ⊢
  obtain ⟨h1, h2⟩ := hn
  have h2' : n ≤ x₀ := by rwa [hx₀] at h2
  have hxle : (x₀:ℝ) ≤ X := by
    have h := Int.floor_le X
    rw [hx₀] at h
    exact h
  have hceil : X - H ≤ ((⌈X - H⌉ : ℤ) : ℝ) := Int.le_ceil (X - H)
  have h4 : ((⌈X - H⌉ : ℤ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
  have hA : (n:ℝ) ≥ X - H := le_trans hceil h4
  have hlow : (x₀:ℝ) - (((M-1:ℕ)):ℝ) ≤ (n:ℝ) := by
    have hMM : (((M-1:ℕ)):ℝ) = (M:ℝ) - 1 := by
      push_cast [Nat.cast_sub hM2]
      ring
    rw [hMM]
    linarith
  have h7 : x₀ - (((M-1:ℕ)):ℤ) ≤ n := by exact_mod_cast hlow
  have h8 : x₀ ≤ x₀ + (((M-1:ℕ)):ℤ) := by
    have : (0:ℤ) ≤ (((M-1:ℕ)):ℤ) := by exact_mod_cast Nat.zero_le _
    omega
  omega

theorem w_nonneg {M : ℕ} (x₀ : ℤ) (n : ℤ) :
    (0:ℝ) ≤ 2 * max 0 (1 - |(n:ℝ) - (x₀:ℝ)|/(M:ℝ)) := by
  have := le_max_left (0:ℝ) (1 - |(n:ℝ) - (x₀:ℝ)|/(M:ℝ))
  linarith

/-- On the window the tent weight is at least `1`. -/
theorem w_ge_one {X H : ℝ} (hH : 1 ≤ H) {M : ℕ}
    (hM2 : 2*H + 2 ≤ (M:ℝ)) {x₀ : ℤ}
    (hx₀ : (⌊X⌋ : ℤ) = x₀) {n : ℤ} (hn : n ∈ win X H) :
    1 ≤ 2 * max 0 (1 - |(n:ℝ) - (x₀:ℝ)|/(M:ℝ)) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by linarith
  simp only [win, Finset.mem_Icc] at hn
  obtain ⟨h1, h2⟩ := hn
  have h2' : n ≤ x₀ := by rwa [hx₀] at h2
  have hxle : (x₀:ℝ) ≤ X := by
    have h := Int.floor_le X
    rw [hx₀] at h
    exact h
  have hceil : X - H ≤ ((⌈X - H⌉ : ℤ) : ℝ) := Int.le_ceil (X - H)
  have h4 : ((⌈X - H⌉ : ℤ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
  have hA : (n:ℝ) ≥ X - H := le_trans hceil h4
  have h5 : (n:ℝ) ≤ (x₀:ℝ) := by exact_mod_cast h2'
  have hd : |(n:ℝ) - (x₀:ℝ)| ≤ H := by
    rw [abs_le]
    constructor <;> linarith
  have hd2 : |(n:ℝ) - (x₀:ℝ)| / (M:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hM0]
    linarith
  have hpos : (0:ℝ) ≤ 1 - |(n:ℝ) - (x₀:ℝ)|/(M:ℝ) := by linarith
  rw [max_eq_right hpos]
  linarith

/-! ### 17. The convolution as an integral, and its conjugate -/

theorem conj_char (θ : ℝ) (n : ℤ) : starRingEnd ℂ (𝕖 θ n) = 𝕖 (-θ) n := by
  have h := conj_exp_char θ n
  rw [show 𝕖 θ n = Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (n:ℂ)) from rfl, h]
  congr 1
  push_cast
  ring

/-- `conv n` is the integral of the product of the two transforms against `𝕖 (-x) n`. -/
theorem conv_eq_integral (S : Finset ℤ) (f g : ℤ → ℝ) (hg : SuppIn S g) (n : ℤ) :
    (conv S f g n : ℂ)
      = ∫ x in (0:ℝ)..1, (fhat S f x * fhat S g x) * 𝕖 (-x) n := by
  rw [inversion S f g hg n]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show fhat S f x * fhat S g x
      * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * ((-n : ℤ):ℂ))
    = (fhat S f x * fhat S g x)
      * Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ):ℂ) * (n:ℂ))
  rw [show (2:ℂ) * Real.pi * Complex.I * (x:ℂ) * ((-n : ℤ):ℂ)
      = 2 * Real.pi * Complex.I * ((-x : ℝ):ℂ) * (n:ℂ) from by push_cast; ring]

/-- The same integral with the conjugate of the product. -/
theorem conj_conv_eq_integral (S : Finset ℤ) (f g : ℤ → ℝ) (hg : SuppIn S g) (n : ℤ) :
    (conv S f g n : ℂ)
      = ∫ y in (0:ℝ)..1, (starRingEnd ℂ (fhat S f y * fhat S g y)) * 𝕖 y n := by
  have h1 : starRingEnd ℂ (∫ y in (0:ℝ)..1,
        (starRingEnd ℂ (fhat S f y * fhat S g y)) * 𝕖 y n)
      = ∫ y in (0:ℝ)..1, (fhat S f y * fhat S g y) * 𝕖 (-y) n := by
    rw [interval_conj]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [map_mul, Complex.conj_conj, conj_char]
  have h2 : starRingEnd ℂ (∫ y in (0:ℝ)..1,
        (starRingEnd ℂ (fhat S f y * fhat S g y)) * 𝕖 y n) = (conv S f g n : ℂ) := by
    rw [h1]
    exact (conv_eq_integral S f g hg n).symm
  have h3 : starRingEnd ℂ (conv S f g n : ℂ)
      = ∫ y in (0:ℝ)..1, (starRingEnd ℂ (fhat S f y * fhat S g y)) * 𝕖 y n := by
    rw [← h2, Complex.conj_conj]
  rw [← h3, Complex.conj_ofReal]

/-! ### 18. Fubini and monotonicity for the unit square -/

/-- Integrability of the parametric integral over the unit interval. -/
theorem intervalIntegrable_parametric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : ℝ → ℝ → E}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    IntervalIntegrable (fun x : ℝ => ∫ y in (0:ℝ)..1, F x y) volume 0 1 := by
  have hInt : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict (Set.uIoc (0:ℝ) 1))) := by
    have h1 : Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le (by norm_num)
    rw [h1, Measure.prod_restrict]
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hleft := hInt.integral_prod_left
  rw [intervalIntegrable_iff]
  refine hleft.congr ?_
  filter_upwards with x
  rw [intervalIntegral.integral_of_le (by norm_num), Set.uIoc_of_le (by norm_num)]
  rfl

/-- Monotonicity of the iterated integral over the unit square. -/
theorem double_mono {F G : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, F x y ≤ G x y) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F x y)
      ≤ ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, G x y := by
  have hinner : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (∫ y in (0:ℝ)..1, F x y) ≤ ∫ y in (0:ℝ)..1, G x y := by
    intro x hx
    have h1 : IntervalIntegrable (fun y : ℝ => F x y) volume 0 1 :=
      (hF.comp (by fun_prop : Continuous fun y : ℝ => (x, y))).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun y : ℝ => G x y) volume 0 1 :=
      (hG.comp (by fun_prop : Continuous fun y : ℝ => (x, y))).intervalIntegrable _ _
    exact intervalIntegral.integral_mono_on (by norm_num) h1 h2 (fun y hy => h x hx y hy)
  exact intervalIntegral.integral_mono_on (by norm_num)
    (intervalIntegrable_parametric hF) (intervalIntegrable_parametric hG) hinner

/-- Additivity of the iterated integral over the unit square. -/
theorem double_add {F G : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (F x y + G x y))
      = (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F x y)
        + ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, G x y := by
  have hinner : ∀ x : ℝ, (∫ y in (0:ℝ)..1, (F x y + G x y))
      = (∫ y in (0:ℝ)..1, F x y) + ∫ y in (0:ℝ)..1, G x y := by
    intro x
    have h1 : IntervalIntegrable (fun y : ℝ => F x y) volume 0 1 :=
      (hF.comp (by fun_prop : Continuous fun y : ℝ => (x, y))).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun y : ℝ => G x y) volume 0 1 :=
      (hG.comp (by fun_prop : Continuous fun y : ℝ => (x, y))).intervalIntegrable _ _
    exact intervalIntegral.integral_add h1 h2
  simp_rw [hinner]
  exact intervalIntegral.integral_add (intervalIntegrable_parametric hF)
    (intervalIntegrable_parametric hG)

/-- Pulling a constant out of the iterated integral. -/
theorem double_const_mul (c : ℝ) {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, c * F x y)
      = c * ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F x y := by
  have hinner : ∀ x : ℝ, (∫ y in (0:ℝ)..1, c * F x y) = c * ∫ y in (0:ℝ)..1, F x y := by
    intro x
    exact intervalIntegral.integral_const_mul c _
  simp_rw [hinner]
  exact intervalIntegral.integral_const_mul c _

/-- Fubini for the unit square, real-valued. -/
theorem double_swap {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F x y)
      = ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, F x y := by
  refine intervalIntegral_intervalIntegral_swap ?_
  have h1 : Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le (by norm_num)
  rw [h1]
  exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-! ### 19. The AM-GM step for the double integral -/

theorem double_amgm_le {f g : ℝ → ℂ} {W : ℝ → ℂ} {C : ℝ}
    (hfc : Continuous f) (hgc : Continuous g) (hWc : Continuous W)
    (hWeven : ∀ θ : ℝ, ‖W (-θ)‖ = ‖W θ‖)
    (hKg : ∀ c : ℝ, (∫ y in (0:ℝ)..1, ‖g y‖ ^ 2 * ‖W (y - c)‖) ≤ C)
    (hC0 : 0 ≤ C) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖f x‖ * ‖g x‖ * (‖f y‖ * ‖g y‖) * ‖W (y - x)‖)
      ≤ C * ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2 := by
  have hfn : Continuous fun x : ℝ => ‖f x‖ ^ 2 := hfc.norm.pow 2
  have hgn : Continuous fun x : ℝ => ‖g x‖ ^ 2 := hgc.norm.pow 2
  -- continuity of the corner integrands
  have hLc : Continuous fun p : ℝ × ℝ =>
      ‖f p.1‖ * ‖g p.1‖ * (‖f p.2‖ * ‖g p.2‖) * ‖W (p.2 - p.1)‖ := by fun_prop
  have hUc : Continuous fun p : ℝ × ℝ => ‖f p.1‖^2 * ‖g p.2‖^2 * ‖W (p.2 - p.1)‖ := by fun_prop
  have hVc : Continuous fun p : ℝ × ℝ => ‖g p.1‖^2 * ‖f p.2‖^2 * ‖W (p.2 - p.1)‖ := by fun_prop
  -- the pointwise AM-GM
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      ‖f x‖ * ‖g x‖ * (‖f y‖ * ‖g y‖) * ‖W (y - x)‖
        ≤ (1/2) * ((‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖)
            + (‖g x‖^2 * ‖f y‖^2 * ‖W (y - x)‖)) := by
    intro x _ y _
    have hk0 : (0:ℝ) ≤ ‖W (y - x)‖ := norm_nonneg _
    have ham : 2 * (‖f x‖ * ‖g y‖) * (‖g x‖ * ‖f y‖) ≤ (‖f x‖ * ‖g y‖)^2 + (‖g x‖ * ‖f y‖)^2 := by
      nlinarith [sq_nonneg (‖f x‖ * ‖g y‖ - ‖g x‖ * ‖f y‖)]
    have hprod : ‖f x‖ * ‖g x‖ * (‖f y‖ * ‖g y‖) * ‖W (y - x)‖
        = ((‖f x‖ * ‖g y‖) * (‖g x‖ * ‖f y‖)) * ‖W (y - x)‖ := by ring
    rw [hprod]
    nlinarith [ham, hk0, sq_nonneg (‖f x‖ * ‖g y‖), sq_nonneg (‖g x‖ * ‖f y‖)]
  have hSc : Continuous fun p : ℝ × ℝ =>
      (‖f p.1‖^2 * ‖g p.2‖^2 * ‖W (p.2 - p.1)‖)
        + (‖g p.1‖^2 * ‖f p.2‖^2 * ‖W (p.2 - p.1)‖) := by fun_prop
  have hHc : Continuous fun p : ℝ × ℝ =>
      (1/2) * ((‖f p.1‖^2 * ‖g p.2‖^2 * ‖W (p.2 - p.1)‖)
        + (‖g p.1‖^2 * ‖f p.2‖^2 * ‖W (p.2 - p.1)‖)) := by fun_prop
  -- step 1: monotonicity
  have hstep1 := double_mono hLc hHc hpt
  -- step 2: linearity
  have hlin : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        (1/2) * ((‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖)
          + (‖g x‖^2 * ‖f y‖^2 * ‖W (y - x)‖)))
      = (1/2) * ((∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖)
        + ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖g x‖^2 * ‖f y‖^2 * ‖W (y - x)‖) := by
    rw [double_const_mul (1/2) hSc]
    congr 1
    exact double_add hUc hVc
  -- step 3: the `f`-weighted term
  have hJU : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖)
      ≤ C * ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2 := by
    have hinner : ∀ x ∈ Set.Icc (0:ℝ) 1,
        (∫ y in (0:ℝ)..1, ‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖) ≤ C * ‖f x‖^2 := by
      intro x _
      have h1 : (∫ y in (0:ℝ)..1, ‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖)
          = ‖f x‖^2 * ∫ y in (0:ℝ)..1, ‖g y‖^2 * ‖W (y - x)‖ := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun y _ => ?_
        ring
      rw [h1]
      have := hKg x
      have hfn0 : (0:ℝ) ≤ ‖f x‖^2 := by positivity
      nlinarith [this, hfn0]
    have hi1 : IntervalIntegrable (fun x : ℝ =>
        ∫ y in (0:ℝ)..1, ‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖) volume 0 1 :=
      intervalIntegrable_parametric hUc
    have hi2 : IntervalIntegrable (fun x : ℝ => C * ‖f x‖^2) volume 0 1 :=
      (continuous_const.mul hfn).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by norm_num) hi1 hi2 hinner
    have h2 : (∫ x in (0:ℝ)..1, C * ‖f x‖^2) = C * ∫ x in (0:ℝ)..1, ‖f x‖^2 :=
      intervalIntegral.integral_const_mul C _
    linarith [hmono, h2]
  -- step 4: the `g`-weighted term equals the `f`-weighted one
  have hJV : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖g x‖^2 * ‖f y‖^2 * ‖W (y - x)‖)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖ := by
    have hV'c : Continuous fun p : ℝ × ℝ => ‖g p.1‖^2 * ‖f p.2‖^2 * ‖W (p.1 - p.2)‖ := by
      fun_prop
    have heven : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖g x‖^2 * ‖f y‖^2 * ‖W (y - x)‖)
        = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖g x‖^2 * ‖f y‖^2 * ‖W (x - y)‖ := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [show ‖W (y - x)‖ = ‖W (x - y)‖ from by
        rw [show x - y = -(y - x) from by ring, hWeven]]
    rw [heven, double_swap hV'c]
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  -- step 5: assemble
  have hstep2 : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        (1/2) * ((‖f x‖^2 * ‖g y‖^2 * ‖W (y - x)‖)
          + (‖g x‖^2 * ‖f y‖^2 * ‖W (y - x)‖))) ≤ C * ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2 := by
    rw [hlin]
    rw [hJV]
    linarith [hJU]
  linarith [hstep1, hstep2]

/-! ### 20. The norm bound for the master double integral -/

theorem double_norm_le {A : ℝ → ℂ} {W : ℝ → ℂ}
    (hAc : Continuous A) (hWc : Continuous W) :
    ‖∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, A x * (starRingEnd ℂ (A y)) * W (y - x)‖
      ≤ ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖A x‖ * ‖A y‖ * ‖W (y - x)‖ := by
  have hFc : Continuous fun p : ℝ × ℝ =>
      A p.1 * (starRingEnd ℂ (A p.2)) * W (p.2 - p.1) := by fun_prop
  have hGc : Continuous fun p : ℝ × ℝ => ‖A p.1‖ * ‖A p.2‖ * ‖W (p.2 - p.1)‖ := by fun_prop
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      ‖A x * (starRingEnd ℂ (A y)) * W (y - x)‖ = ‖A x‖ * ‖A y‖ * ‖W (y - x)‖ := by
    intro x _ y _
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have hinner : ∀ x ∈ Set.Icc (0:ℝ) 1,
      ‖∫ y in (0:ℝ)..1, A x * (starRingEnd ℂ (A y)) * W (y - x)‖
        ≤ ∫ y in (0:ℝ)..1, ‖A x‖ * ‖A y‖ * ‖W (y - x)‖ := by
    intro x hx
    have h1 : ‖∫ y in (0:ℝ)..1, A x * (starRingEnd ℂ (A y)) * W (y - x)‖
        ≤ ∫ y in (0:ℝ)..1, ‖A x * (starRingEnd ℂ (A y)) * W (y - x)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    refine le_trans h1 ?_
    exact le_of_eq (intervalIntegral.integral_congr fun y hy =>
      hpt x hx y (by rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy))
  have hi1 : IntervalIntegrable (fun x : ℝ =>
      ‖∫ y in (0:ℝ)..1, A x * (starRingEnd ℂ (A y)) * W (y - x)‖) volume 0 1 :=
    (intervalIntegrable_parametric hFc).norm
  have hi2 : IntervalIntegrable (fun x : ℝ =>
      ∫ y in (0:ℝ)..1, ‖A x‖ * ‖A y‖ * ‖W (y - x)‖) volume 0 1 :=
    intervalIntegrable_parametric hGc
  calc ‖∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, A x * (starRingEnd ℂ (A y)) * W (y - x)‖
      ≤ ∫ x in (0:ℝ)..1, ‖∫ y in (0:ℝ)..1, A x * (starRingEnd ℂ (A y)) * W (y - x)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖A x‖ * ‖A y‖ * ‖W (y - x)‖ :=
        intervalIntegral.integral_mono_on (by norm_num) hi1 hi2 hinner

/-! ### 21. The leaf -/

theorem leaf_short_second_moment_bound_proved :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      (∀ (S : Finset ℤ) (f g : ℤ → ℝ) (X H Δ : ℝ), 1 ≤ H → SuppIn S f → SuppIn S g →
        FourierClose S H Δ g → ∑ n ∈ win X H, conv S f g n ^ 2 ≤ C0 * H * sqn S f * Δ) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro S f g X H Δ hH hf hg hclose
  have hΔ : 0 ≤ Δ := fourierClose_delta_nonneg hH hclose
  have hH0 : (0:ℝ) < H := by linarith
  -- the parameters
  set M : ℕ := Nat.ceil (2*H) + 4 with hMdef
  have hM1 : 1 ≤ M := by omega
  have hMge : 2*H ≤ (M:ℝ) := by
    have h1 : 2*H ≤ ((Nat.ceil (2*H) : ℕ) : ℝ) := Nat.le_ceil (2*H)
    rw [hMdef]; push_cast; linarith
  have hMge2 : 2*H + 2 ≤ (M:ℝ) := by
    have h1 : 2*H ≤ ((Nat.ceil (2*H) : ℕ) : ℝ) := Nat.le_ceil (2*H)
    rw [hMdef]; push_cast; linarith
  have hMle : (M:ℝ) ≤ 2*H + 5 := by
    have h1 : ((Nat.ceil (2*H) : ℕ) : ℝ) < 2*H + 1 := Nat.ceil_lt_add_one (by linarith)
    rw [hMdef]; push_cast; linarith
  set x₀ : ℤ := ⌊X⌋ with hx₀
  have hx₀' : (⌊X⌋ : ℤ) = x₀ := hx₀.symm
  set w : ℤ → ℝ := fun n => 2 * max 0 (1 - |(n:ℝ) - (x₀:ℝ)|/(M:ℝ)) with hw
  set Rf : Finset ℤ := Finset.Icc (x₀ - (((M-1:ℕ)):ℤ)) (x₀ + (((M-1:ℕ)):ℤ)) with hRf
  set Wf : ℝ → ℂ := fun θ => ∑ n ∈ Rf, ((w n : ℝ) : ℂ) * 𝕖 θ n with hWf
  -- the four kernel facts
  have hWc : Continuous Wf := by
    simp only [hWf, hw, hRf]
    exact tent_kernel_continuous M x₀
  have hWper : ∀ θ : ℝ, Wf (θ + 1) = Wf θ := by
    intro θ
    simp only [hWf, hRf, hw]
    exact tent_kernel_periodic x₀ θ
  have hWnorm : ∀ θ : ℝ, ‖Wf θ‖ ≤ 2*(M:ℝ) := by
    intro θ
    simp only [hWf, hRf, hw]
    exact tent_kernel_norm_le hM1 x₀ θ
  have hWdec : ∀ θ : ℝ, 0 < |θ| → |θ| ≤ 1/2 → ‖Wf θ‖ * (2*(M:ℝ)) * θ^2 ≤ 1 := by
    intro θ h1 h2
    simp only [hWf, hRf, hw]
    exact tent_kernel_decay_le hM1 x₀ h1 h2
  have hWeven : ∀ θ : ℝ, ‖Wf (-θ)‖ = ‖Wf θ‖ := by
    intro θ
    have hcoe : Wf (-θ) = starRingEnd ℂ (Wf θ) := by
      simp only [hWf]
      rw [map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul, Complex.conj_ofReal]
      congr 1
      show Complex.exp (2 * Real.pi * Complex.I * ((-θ:ℝ):ℂ) * (n:ℂ))
        = starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ) * (n:ℂ)))
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_intCast]
      push_cast
      ring
    rw [hcoe, Complex.norm_conj]
  -- local control of `‖fhat S g‖²`
  have hQloc : ∀ a : ℝ, (∫ x in a..(a + 2/H), ‖fhat S g x‖ ^ 2) ≤ Δ := by
    intro a
    have h := hclose (a + 1/H)
    have hcomp := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => ‖fhat S g x‖ ^ 2) (a := (-(1/H):ℝ)) (b := (1/H:ℝ)) (a + 1/H)
    rw [show -(1/H) + (a + 1/H) = a from by ring,
      show 1/H + (a + 1/H) = a + 2/H from by ring] at hcomp
    rw [← hcomp]
    refine le_trans (le_of_eq ?_) h
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [add_comm]
  -- the kernel estimate
  have hKg : ∀ c : ℝ, (∫ y in (0:ℝ)..1, ‖fhat S g y‖ ^ 2 * ‖Wf (y - c)‖) ≤ 40*H*Δ := by
    intro c
    exact kernel_estimate' hH hΔ hMge hMle ((continuous_fhat' S g).norm.pow 2)
      (fun y => sq_nonneg _) (fhat_normsq_periodic S g) hQloc hWc hWper hWnorm hWdec c
  -- step 1: the window is inside the weighted range, where the weight is at least one
  have hstep1 : (∑ n ∈ win X H, conv S f g n ^ 2) ≤ ∑ n ∈ Rf, w n * conv S f g n ^ 2 := by
    have h1 : (∑ n ∈ win X H, conv S f g n ^ 2) ≤ ∑ n ∈ win X H, w n * conv S f g n ^ 2 := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hw1 := w_ge_one hH hMge2 hx₀' hn
      have h2 : (0:ℝ) ≤ conv S f g n ^ 2 := sq_nonneg _
      have h3 := mul_le_mul_of_nonneg_right hw1 h2
      linarith
    refine le_trans h1 ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · rw [hRf]
      exact win_subset_R hH hx₀' (by linarith)
    · intro n _ _
      exact mul_nonneg (w_nonneg x₀ n) (sq_nonneg _)
  -- step 2: the weighted sum is the norm of its complex form
  have hcast : ((∑ n ∈ Rf, w n * conv S f g n ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ Rf, (w n : ℂ) * ((conv S f g n : ℂ) ^ 2) := by
    push_cast
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have hnorm : ‖∑ n ∈ Rf, (w n : ℂ) * ((conv S f g n : ℂ) ^ 2)‖
      = ∑ n ∈ Rf, w n * conv S f g n ^ 2 := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg (fun n _ => mul_nonneg (w_nonneg x₀ n) (sq_nonneg _))
  -- step 3: the master identity
  have hmast : (∑ n ∈ Rf, (w n : ℂ) * ((conv S f g n : ℂ) ^ 2))
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
          (fhat S f x * fhat S g x) * (starRingEnd ℂ (fhat S f y * fhat S g y))
            * Wf (y - x) := by
    have hws := weighted_sum_double (R := Rf)
      (A := fun x : ℝ => fhat S f x * fhat S g x)
      (B := fun y : ℝ => starRingEnd ℂ (fhat S f y * fhat S g y))
      (w := w) (W := Wf) (ch := 𝕖)
      (fun n => continuous_exp_char n)
      (fun x y n => by
        show Complex.exp (2 * Real.pi * Complex.I * ((y - x : ℝ):ℂ) * (n:ℂ))
          = Complex.exp (2 * Real.pi * Complex.I * (y:ℂ) * (n:ℂ))
            * Complex.exp (2 * Real.pi * Complex.I * ((-x:ℝ):ℂ) * (n:ℂ))
        rw [show (2:ℂ) * Real.pi * Complex.I * ((y - x : ℝ):ℂ) * (n:ℂ)
            = 2 * Real.pi * Complex.I * (y:ℂ) * (n:ℂ)
              + 2 * Real.pi * Complex.I * ((-x:ℝ):ℂ) * (n:ℂ) from by push_cast; ring,
          Complex.exp_add])
      (fun θ => rfl)
      ((continuous_fhat' S f).mul (continuous_fhat' S g))
      (((continuous_fhat' S f).mul (continuous_fhat' S g)).star)
    rw [← hws]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pow_two]
    nth_rewrite 1 [conv_eq_integral S f g hg n]
    rw [conj_conv_eq_integral S f g hg n]
  -- step 4: the double-integral bound
  have hAnorm : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        ‖fhat S f x * fhat S g x‖ * ‖fhat S f y * fhat S g y‖ * ‖Wf (y - x)‖)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
          ‖fhat S f x‖ * ‖fhat S g x‖ * (‖fhat S f y‖ * ‖fhat S g y‖) * ‖Wf (y - x)‖ := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [norm_mul, norm_mul]
  have hnorm_bound : ‖∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        (fhat S f x * fhat S g x) * (starRingEnd ℂ (fhat S f y * fhat S g y)) * Wf (y - x)‖
      ≤ ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
          ‖fhat S f x‖ * ‖fhat S g x‖ * (‖fhat S f y‖ * ‖fhat S g y‖) * ‖Wf (y - x)‖ := by
    rw [← hAnorm]
    exact double_norm_le ((continuous_fhat' S f).mul (continuous_fhat' S g)) hWc
  have hamgm := double_amgm_le (f := fun x : ℝ => fhat S f x) (g := fun x : ℝ => fhat S g x)
    (W := Wf) (continuous_fhat' S f) (continuous_fhat' S g) hWc hWeven hKg
    (mul_nonneg (by linarith : (0:ℝ) ≤ 40*H) hΔ)
  have hpl : (∫ x in (0:ℝ)..1, ‖fhat S f x‖ ^ 2) = sqn S f := by
    rw [← plancherel S f]
    exact intervalIntegral.integral_congr fun x _ => (Complex.normSq_eq_norm_sq _).symm
  -- assembly
  have hsq : (0:ℝ) ≤ sqn S f := sqn_nonneg S f
  have hHΔ : (0:ℝ) ≤ H * Δ := mul_nonneg (by linarith) hΔ
  have hfinal : (∑ n ∈ Rf, w n * conv S f g n ^ 2) ≤ 40*H*Δ * sqn S f := by
    rw [← hnorm, hmast]
    refine le_trans hnorm_bound ?_
    rw [← hpl]
    linarith [hamgm]
  nlinarith [hstep1, hfinal, hsq, hHΔ, hH]

end

end LeanLab.Grimmelt2019.DecompJ227WIP2


namespace LeanLab.Grimmelt2019.Decomp

open Real
open LeanLab.Grimmelt2019.Prop21
open MeasureTheory
open Complex

/-- LEAF page 6: Schwartz majorant exists. -/
theorem leaf_schwartz_exists : ∃ (Φ : ℝ → ℝ), (∀ x ∈ Set.Icc (-1 : ℝ) 1, 1 ≤ Φ x) ∧
  (∀ x, 0 ≤ Φ x) := by
  use fun _ => 1
  constructor
  · intro x _
    linarith
  · intro x
    linarith

/-- LEAF page 6: The sum over n in [X - H, X] of the square of f * g at n is at most C0 H times the squared norm of f times the sup over α of the integral over β in [-1/H, 1/H] of the square of the absolute value of ĝ at α + β. -/
theorem leaf_short_second_moment_bound : ∃ C0 : ℝ, 0 ≤ C0 ∧
  (∀ (S : Finset ℤ) (f g : ℤ → ℝ) (X H Δ : ℝ), 1 ≤ H → SuppIn S f → SuppIn S g →
    FourierClose S H Δ g → ∑ n ∈ win X H, conv S f g n ^ 2 ≤ C0 * H * sqn S f * Δ) :=
  LeanLab.Grimmelt2019.DecompJ227WIP2.leaf_short_second_moment_bound_proved

/-- The assembly theorem. -/
theorem shortSecondMoment_proved : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0 := by
  have h := leaf_short_second_moment_bound
  rcases h with ⟨C0, hC0, hbound⟩
  use C0
  constructor
  · exact hC0
  · intro S f g X H Δ hH hf hg hclose
    exact hbound S f g X H Δ hH hf hg hclose

end LeanLab.Grimmelt2019.Decomp
