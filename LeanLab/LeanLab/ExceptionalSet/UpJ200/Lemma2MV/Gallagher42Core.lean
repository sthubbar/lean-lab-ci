import Mathlib
import LeanLab.ExceptionalSet.State1539Data264

/-!
# A discrete Gallagher lemma, the analysis behind P0015 Lemma 4.2

Source P0015, Montgomery and Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27, 1975, 353-370, Lemma 4.2 on page 357, Gallagher's Lemma 1, as used in the first
display of section 7 on page 366.

For coefficients `a n` on a finite set `s` of naturals put `S(η) = Σ a n e(nη)` and, for an
integer `H ≥ 1`, `B(m) = Σ_{m-H<n≤m} a n`. Then `S(η) Σ_{j<H} e(jη) = Σ_m B(m) e(mη)`,
Parseval for trigonometric polynomials on a unit period gives `∫ |S D_H|² = Σ |B(m)|²`, and
`|D_H(η)| ≥ H/2` for `|η| H ≤ 1/8`. Hence `∫_{-κ}^{κ} |S|² ≤ 4 H⁻² Σ_m |B(m)|²` when `κ H ≤ 1/8`.
This discrete form avoids Plancherel on the real line.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MV

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)

/-- The exponential sum `S(η) = Σ_{n∈s} a n e(nη)` of P0015 Lemma 4.2, page 357. -/
noncomputable def gall42_S (s : Finset ℕ) (a : ℕ → ℂ) (η : ℝ) : ℂ :=
  ∑ n ∈ s, a n * eC (η * n)

/-- The block sum `B(m) = Σ_{m-H<n≤m} a n` of P0015 Lemma 4.2, page 357, with `n` in `s`. -/
noncomputable def gall42_B (s : Finset ℕ) (a : ℕ → ℂ) (H m : ℕ) : ℂ :=
  ∑ n ∈ s.filter (fun n => n ≤ m ∧ m < n + H), a n

/-- Continuity of `e(x)`, used for every integral in P0015 Lemma 4.2, page 357. -/
lemma gall42_continuous_eC : Continuous eC := by
  unfold eC; fun_prop

/-- Additivity `e(x) e(y) = e(x + y)`, P0015 page 354 notation. -/
lemma gall42_eC_add (x y : ℝ) : eC x * eC y = eC (x + y) := by
  unfold eC; rw [← Complex.exp_add]; push_cast; ring_nf

/-- Conjugation `conj e(x) = e(-x)`, P0015 page 354 notation. -/
lemma gall42_conj_eC (x : ℝ) : starRingEnd ℂ (eC x) = eC (-x) := by
  unfold eC; rw [← Complex.exp_conj]; congr 1
  simp [Complex.conj_ofReal, map_ofNat]

/-- Orthogonality `∫_{-1/2}^{1/2} e(kη) dη` is `1` at `k = 0` and `0` otherwise, the step of
Parseval behind P0015 Lemma 4.2, page 357. -/
lemma gall42_integral_eC_int (k : ℤ) :
    ∫ η in (-(1 / 2 : ℝ))..(1 / 2), eC (η * k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]; norm_num
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, Complex.I_ne_zero, hk']
    have hfun : (fun η : ℝ => eC (η * k)) =
        fun η : ℝ => Complex.exp ((2 * Real.pi * Complex.I * k) * η) := by
      funext η; simp only [eC]; push_cast; ring_nf
    rw [hfun, integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * k) * ((1 / 2 : ℝ) : ℂ)) =
        Complex.exp ((2 * Real.pi * Complex.I * k) * ((-(1 / 2) : ℝ) : ℂ)) := by
      have : (2 * Real.pi * Complex.I * k) * ((1 / 2 : ℝ) : ℂ) =
          (2 * Real.pi * Complex.I * k) * ((-(1 / 2) : ℝ) : ℂ) + k * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h1, sub_self, zero_div]

/-- Parseval for a trigonometric polynomial on a unit period,
`∫_{-1/2}^{1/2} |Σ c m e(mη)|² dη = Σ |c m|²`, used in the proof of P0015 Lemma 4.2, page 357. -/
lemma gall42_parseval (t : Finset ℕ) (c : ℕ → ℂ) :
    ∫ η in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ t, c m * eC (η * m)‖ ^ 2 =
      ∑ m ∈ t, ‖c m‖ ^ 2 := by
  have hcont : ∀ k : ℝ, Continuous (fun η : ℝ => eC (η * k)) := fun k =>
    gall42_continuous_eC.comp (by fun_prop)
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hpt : ∀ η : ℝ, (((‖∑ m ∈ t, c m * eC (η * m)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ m ∈ t, ∑ m' ∈ t, (c m * starRingEnd ℂ (c m')) * eC (η * (((m : ℤ) - m' : ℤ) : ℝ)) := by
    intro η
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl (fun m _ => sum_congr rfl (fun m' _ => ?_))
    rw [map_mul, gall42_conj_eC]
    have : eC (η * m) * eC (-(η * m')) = eC (η * (((m : ℤ) - m' : ℤ) : ℝ)) := by
      rw [gall42_eC_add]; congr 1; push_cast; ring
    rw [← this]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum]
  · push_cast
    refine sum_congr rfl (fun m hm => ?_)
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
      have : ∀ m' ∈ t, c m * starRingEnd ℂ (c m') *
          (∫ η in (-(1 / 2 : ℝ))..(1 / 2), eC (η * ((m : ℝ) - m'))) =
          if m = m' then c m * starRingEnd ℂ (c m') else 0 := by
        intro m' _
        rw [show ((m : ℝ) - m') = (((m : ℤ) - m' : ℤ) : ℝ) by push_cast; ring,
          gall42_integral_eC_int]
        by_cases h : m = m'
        · subst h; simp
        · have : ((m : ℤ) - m' : ℤ) ≠ 0 := by omega
          simp [h, this]
      rw [sum_congr rfl this, Finset.sum_ite_eq, if_pos hm, Complex.mul_conj']
    · intro m' _
      exact ((hcont _).const_mul _ |>.intervalIntegrable _ _)
  · intro m _
    exact (continuous_finsetSum _ (fun m' _ => (hcont _).const_mul _)).intervalIntegrable _ _

/-- The lower bound `|Σ_{j<H} e(jη)| ≥ H/2` for `|η| H ≤ 1/8`, the kernel bound in the proof of
P0015 Lemma 4.2, page 357: each real part `cos 2πjη` is at least `1/2`. -/
lemma gall42_dirichlet_lower (H : ℕ) (η : ℝ) (hη : |η| * H ≤ 1 / 8) :
    (H : ℝ) / 2 ≤ ‖∑ j ∈ range H, eC (η * j)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [Complex.re_sum]
  have hj : ∀ j ∈ range H, (1 / 2 : ℝ) ≤ (eC (η * j)).re := by
    intro j hj
    have hjH : (j : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hj).le
    have hre : (eC (η * j)).re = Real.cos (2 * Real.pi * (η * j)) := by
      unfold eC
      rw [show (2 * (Real.pi : ℂ) * Complex.I * ((η * j : ℝ) : ℂ)) =
        ((2 * Real.pi * (η * j) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_re _
    rw [hre]
    have habs : |2 * Real.pi * (η * j)| ≤ 1 := by
      rw [abs_mul (2 * Real.pi), abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        abs_mul η, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)]
      have h1 : |η| * j ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left hjH (abs_nonneg _)) hη
      have h2 : 2 * Real.pi * (|η| * j) ≤ 2 * Real.pi * (1 / 8) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith [Real.pi_le_four]
    have hsq : (2 * Real.pi * (η * j)) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (2 * Real.pi * (η * j))]
    have := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (η * j))
    linarith
  calc (H : ℝ) / 2 = ∑ j ∈ range H, (1 / 2 : ℝ) := by simp; ring
    _ ≤ _ := sum_le_sum hj

/-- The product identity `S(η) Σ_{j<H} e(jη) = Σ_m B(m) e(mη)` of P0015 Lemma 4.2, page 357,
with `m` running up to `N + H` when every `n` in `s` is below `N`. -/
lemma gall42_mul_identity (s : Finset ℕ) (a : ℕ → ℂ) (N H : ℕ) (hs : ∀ n ∈ s, n < N)
    (η : ℝ) :
    gall42_S s a η * ∑ j ∈ range H, eC (η * j) =
      ∑ m ∈ range (N + H), gall42_B s a H m * eC (η * m) := by
  unfold gall42_S gall42_B
  simp_rw [sum_filter, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun n hn => ?_)
  have hN := hs n hn
  have h1 : ∑ m ∈ range (N + H), (if n ≤ m ∧ m < n + H then a n else 0) * eC (η * m) =
      ∑ m ∈ Ico n (n + H), a n * eC (η * m) := by
    rw [← sum_filter_add_sum_filter_not (range (N + H)) (fun m => n ≤ m ∧ m < n + H)]
    rw [sum_eq_zero (s := (range (N + H)).filter (fun m => ¬ (n ≤ m ∧ m < n + H)))
      (fun m hm => by rw [if_neg (mem_filter.mp hm).2, zero_mul]), add_zero]
    have hset : (range (N + H)).filter (fun m => n ≤ m ∧ m < n + H) = Ico n (n + H) := by
      ext m; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [← hset]
    refine sum_congr rfl (fun m hm => ?_)
    rw [if_pos (mem_filter.mp hm).2]
  rw [h1, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [mul_assoc, gall42_eC_add]
  congr 2; push_cast; ring

/-- Continuity of `S`, for the integrals of P0015 Lemma 4.2, page 357. -/
lemma gall42_continuous_S (s : Finset ℕ) (a : ℕ → ℂ) : Continuous (gall42_S s a) := by
  unfold gall42_S
  exact continuous_finsetSum _ (fun n _ =>
    continuous_const.mul (gall42_continuous_eC.comp (by fun_prop)))

/-- The discrete Gallagher inequality behind P0015 Lemma 4.2, page 357:
`∫_{-κ}^{κ} |S|² ≤ 4 H⁻² Σ_{m<N+H} |B(m)|²` when `κ H ≤ 1/8` and `H ≥ 1`. -/
theorem gall42_gallagher (s : Finset ℕ) (a : ℕ → ℂ) (N H : ℕ) (hs : ∀ n ∈ s, n < N)
    (hH : 1 ≤ H) (κ : ℝ) (hκ : 0 ≤ κ) (hκH : κ * H ≤ 1 / 8) :
    ∫ η in (-κ)..κ, ‖gall42_S s a η‖ ^ 2 ≤
      4 / (H : ℝ) ^ 2 * ∑ m ∈ range (N + H), ‖gall42_B s a H m‖ ^ 2 := by
  set G : ℝ → ℂ := fun η => ∑ m ∈ range (N + H), gall42_B s a H m * eC (η * m) with hG
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hGc : Continuous G := continuous_finsetSum _ (fun m _ =>
    continuous_const.mul (gall42_continuous_eC.comp (by fun_prop)))
  have hSc := gall42_continuous_S s a
  have hpt : ∀ η ∈ Set.Icc (-κ) κ, ‖gall42_S s a η‖ ^ 2 ≤ 4 / (H : ℝ) ^ 2 * ‖G η‖ ^ 2 := by
    intro η hη
    have habs : |η| ≤ κ := abs_le.mpr ⟨hη.1, hη.2⟩
    have hηH : |η| * H ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_right habs hHpos.le) hκH
    have hD := gall42_dirichlet_lower H η hηH
    have hGeq : G η = gall42_S s a η * ∑ j ∈ range H, eC (η * j) :=
      (gall42_mul_identity s a N H hs η).symm
    have hnorm : ‖G η‖ = ‖gall42_S s a η‖ * ‖∑ j ∈ range H, eC (η * j)‖ := by
      rw [hGeq, norm_mul]
    have hS0 := norm_nonneg (gall42_S s a η)
    have h1 : ‖gall42_S s a η‖ * ((H : ℝ) / 2) ≤ ‖G η‖ := by
      rw [hnorm]; exact mul_le_mul_of_nonneg_left hD hS0
    have h2 : (‖gall42_S s a η‖ * ((H : ℝ) / 2)) ^ 2 ≤ ‖G η‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hκ2 : κ ≤ 1 / 2 := by nlinarith
  calc ∫ η in (-κ)..κ, ‖gall42_S s a η‖ ^ 2
      ≤ ∫ η in (-κ)..κ, 4 / (H : ℝ) ^ 2 * ‖G η‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ hpt
        · exact ((continuous_norm.comp hSc).pow 2).intervalIntegrable _ _
        · exact (continuous_const.mul ((continuous_norm.comp hGc).pow 2)).intervalIntegrable _ _
    _ = 4 / (H : ℝ) ^ 2 * ∫ η in (-κ)..κ, ‖G η‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ 4 / (H : ℝ) ^ 2 * ∫ η in (-(1 / 2 : ℝ))..(1 / 2), ‖G η‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) hκ2
          (Filter.Eventually.of_forall (fun η => by positivity)) ?_
        exact ((continuous_norm.comp hGc).pow 2).intervalIntegrable _ _
    _ = 4 / (H : ℝ) ^ 2 * ∑ m ∈ range (N + H), ‖gall42_B s a H m‖ ^ 2 := by
        rw [hG, gall42_parseval]

#print axioms gall42_gallagher

end LeanLab.ExceptionalSet.UpJ200.Lemma2MV
