/-
Split of `leaf_fejer_majorant` in `ExceptionalSet/SPLIT_lemma4.lean` into smaller leaves.

The statement being split is the Fejér-kernel majorant for the indicator of an interval of
fractional parts: the number of `N/2 < n ≤ N` with `z₂ ≤ {αF(n)} < z₁` differs from
`(z₁ - z₂)N/2` by at most `4N/(H+1)` plus the first `H` exponential sums at the frequencies `hα`,
each weighted by `4N/(h+1)`.

`leaf_fejer_majorant_split` below proves that statement from the leaves, with no `sorry` of its own
and without using the target theorem.  The leaves are, in the order the assembly uses them:

1. `leaf_vaaler_trig_majorant` - the per-point step, and the only step with analytic content: for
   every `H` and every interval `[z₂,z₁) ⊆ [0,1]` there is a trigonometric polynomial of degree `H`
   whose coefficients are bounded by `2/(h+1)` and which is within `2/(H+1)` of the indicator at
   every point, in both directions.
2. `leaf_dirichlet_lower` - a lower bound for the exponential sums over the window: among the first
   `N - N/2` frequencies one of the sums has modulus at least 1, so the weighted sum of the sums is
   not smaller than `1/(4N-2)`.  This is what absorbs the additive `1/2` of the window shift.

The assembly then does three things, all elementary: it sums the per-point bound over the window
and bounds the polynomial part by the exponential sums through the triangle inequality, it shifts
the comparison from `N/2` to the exact window length `N - N/2` (off by at most `1/2`), and it
carries out the resulting bookkeeping of constants.

The leaves are open; the assembly is proved.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma4

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. The per-point majorant: for every `H` and every interval `[z₂,z₁) ⊆ [0,1]` there is a
trigonometric polynomial `θ ↦ ∑ h ∈ Icc 1 H, (c h * e(hθ)).re` of degree `H` whose coefficients
satisfy `‖c h‖ ≤ 2/(h+1)` and which differs from the indicator of the interval by at most
`2/(H+1)` at every real point, in absolute value.  Nothing here mentions `N`, `α`, `γ` or a count:
it is one inequality, about one point. -/
theorem leaf_vaaler_trig_majorant (H : ℕ) (z₁ z₂ : ℝ) (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁)
    (hz₁ : z₁ ≤ 1) :
    ∃ c : ℕ → ℂ, (∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) ∧
      ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - (z₁ - z₂)
        - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1) := by
  sorry

/-! ### Auxiliary lemmas for `e(x) = exp(2πix)`, and the linear algebra of the leaves -/

private lemma eC_zero' : eC 0 = 1 := by
  simp [eC]

private lemma eC_add' (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma star_eC' (a : ℝ) : (starRingEnd ℂ) (eC a) = eC (-a) := by
  unfold eC
  have ha : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) = (((2 * Real.pi * a : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have hb : (2 * (Real.pi : ℂ) * Complex.I * ((-a : ℝ) : ℂ)) = (((-(2 * Real.pi * a)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ha, hb, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma norm_eC' (a : ℝ) : ‖eC a‖ = 1 := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) = ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma p_neg_norm (s : Finset ℕ) (x : ℕ → ℝ) (t : ℝ) :
    ‖∑ n ∈ s, eC ((-t) * x n)‖ = ‖∑ n ∈ s, eC (t * x n)‖ := by
  have h1 : (∑ n ∈ s, eC ((-t) * x n)) = (starRingEnd ℂ) (∑ n ∈ s, eC (t * x n)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [star_eC']
    congr 1
    ring
  rw [h1, Complex.norm_conj]

private lemma dirichlet_core (L : ℕ) (hL : 1 ≤ L) (s : Finset ℕ) (hs : s.card = L)
    (x : ℕ → ℝ) (ε : ℝ) (hε : ∀ h ∈ Finset.Icc 1 L, ‖∑ n ∈ s, eC (h * x n)‖ ≤ ε) :
    (1 : ℝ) / 2 ≤ ε := by
  classical
  set p : ℝ → ℂ := fun t => ∑ n ∈ s, eC (t * x n) with hpdef
  have hpev : ∀ t : ℝ, p t = ∑ n ∈ s, eC (t * x n) := fun t => rfl
  obtain ⟨v, hvne, hv⟩ :
      ∃ v : Fin (L + 1) → ℂ, v ≠ 0 ∧ ∀ n ∈ s, ∑ i : Fin (L + 1), v i * eC ((i : ℝ) * x n) = 0 := by
    let f : (Fin (L + 1) → ℂ) →ₗ[ℂ] (↥s → ℂ) :=
      { toFun := fun v n => ∑ i : Fin (L + 1), v i * eC ((i : ℝ) * x n)
        map_add' := by
          intro a b
          funext n
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          funext n
          simp only [Pi.smul_apply, Algebra.smul_def, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring }
    have hnotinj : ¬ Function.Injective f := by
      intro hinj
      have hle := LinearMap.finrank_le_finrank_of_injective hinj
      have h1 : Module.finrank ℂ (Fin (L + 1) → ℂ) = L + 1 := by simp
      have h2 : Module.finrank ℂ (↥s → ℂ) = L := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hs]
      rw [h1, h2] at hle
      omega
    have hex : ∃ a b : Fin (L + 1) → ℂ, f a = f b ∧ a ≠ b := by
      by_contra hcon
      push Not at hcon
      exact hnotinj fun a b hab => hcon a b hab
    obtain ⟨a, b, hab, hne⟩ := hex
    refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
    intro n hn
    have hpt := congrFun hab ⟨n, hn⟩
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib] at hpt ⊢
    rw [← hpt, sub_self]
  have hzero :
      ∑ n ∈ s, (∑ i : Fin (L + 1), v i * eC ((i : ℝ) * x n)) *
        (∑ j : Fin (L + 1), (starRingEnd ℂ) (v j) * eC (-((j : ℝ) * x n))) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have h1 : (∑ j : Fin (L + 1), (starRingEnd ℂ) (v j) * eC (-((j : ℝ) * x n)))
        = (starRingEnd ℂ) (∑ j : Fin (L + 1), v j * eC ((j : ℝ) * x n)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, star_eC']
    rw [h1, hv n hn, map_zero, mul_zero]
  have hexp :
      ∑ n ∈ s, (∑ i : Fin (L + 1), v i * eC ((i : ℝ) * x n)) *
        (∑ j : Fin (L + 1), (starRingEnd ℂ) (v j) * eC (-((j : ℝ) * x n)))
      = ∑ i : Fin (L + 1), ∑ j : Fin (L + 1),
          v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ)) := by
    have hpt : ∀ n : ℕ, (∑ i : Fin (L + 1), v i * eC ((i : ℝ) * x n)) *
        (∑ j : Fin (L + 1), (starRingEnd ℂ) (v j) * eC (-((j : ℝ) * x n)))
        = ∑ i : Fin (L + 1), ∑ j : Fin (L + 1),
            v i * (starRingEnd ℂ) (v j) * eC (((i : ℝ) - (j : ℝ)) * x n) := by
      intro n
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h2 : eC ((i : ℝ) * x n) * eC (-((j : ℝ) * x n)) = eC (((i : ℝ) - (j : ℝ)) * x n) := by
        rw [← eC_add']
        congr 1
        ring
      calc v i * eC ((i : ℝ) * x n) * ((starRingEnd ℂ) (v j) * eC (-((j : ℝ) * x n)))
          = v i * (starRingEnd ℂ) (v j) *
              (eC ((i : ℝ) * x n) * eC (-((j : ℝ) * x n))) := by ring
        _ = v i * (starRingEnd ℂ) (v j) * eC (((i : ℝ) - (j : ℝ)) * x n) := by rw [h2]
    simp only [hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpev, Finset.mul_sum]
  have hdiag :
      ∑ i : Fin (L + 1), ∑ j : Fin (L + 1), v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ))
      = (∑ i : Fin (L + 1), v i * (starRingEnd ℂ) (v i) * p 0)
        + ∑ i : Fin (L + 1), ∑ j ∈ Finset.univ.erase i,
            v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ))) (Finset.mem_univ i)]
    simp only [sub_self]
    rw [add_comm]
  have hp0 : p 0 = (L : ℂ) := by
    rw [hpev]
    simp [hs, eC_zero']
  set S : ℝ := ∑ i : Fin (L + 1), ‖v i‖ ^ 2 with hS
  set T : ℝ := ∑ i : Fin (L + 1), ‖v i‖ with hT
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hSpos : 0 < S := by
    rw [hS]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hvne (funext fun i => by simpa using h i)
    exact Finset.sum_pos' (fun i _ => by positivity)
      ⟨i, Finset.mem_univ i, by
        have hpos : 0 < ‖v i‖ := norm_pos_iff.mpr hi
        positivity⟩
  have hT2 : T ^ 2 ≤ ((L : ℝ) + 1) * S := by
    rw [hT, hS]
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin (L + 1) => ‖v i‖)
    simpa using h
  have hSdef : ((S : ℝ) : ℂ) = ∑ i : Fin (L + 1), v i * (starRingEnd ℂ) (v i) := by
    rw [hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_inj]
    exact (Complex.normSq_eq_norm_sq (v i)).symm
  have hoff :
      ∑ i : Fin (L + 1), ∑ j ∈ Finset.univ.erase i,
          v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ))
      = -(∑ i : Fin (L + 1), v i * (starRingEnd ℂ) (v i) * p 0) := by
    have h0 := hzero
    rw [hexp, hdiag] at h0
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  have hεnn : 0 ≤ ε := by
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 L := by simp [hL]
    exact le_trans (norm_nonneg _) (hε 1 h1)
  have hpair : ∀ i j : Fin (L + 1), i ≠ j → ‖p ((i : ℝ) - (j : ℝ))‖ ≤ ε := by
    intro i j hij
    have hcast : ((i : ℝ) - (j : ℝ)) = ((i.val : ℝ) - (j.val : ℝ)) := by simp
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hlt | hgt
    · have hk1 : 1 ≤ j.val - i.val := by omega
      have hk2 : j.val - i.val ≤ L := by have := j.isLt; omega
      have hsub : ((j.val - i.val : ℕ) : ℝ) = (j.val : ℝ) - (i.val : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
      have hkey : ((i : ℝ) - (j : ℝ)) = -(((j.val - i.val : ℕ)) : ℝ) := by
        rw [hcast, hsub]; ring
      rw [hkey]
      have hnn : ‖p (-(((j.val - i.val : ℕ)) : ℝ))‖ = ‖p (((j.val - i.val : ℕ)) : ℝ)‖ := by
        have := p_neg_norm s x (((j.val - i.val : ℕ)) : ℝ)
        simp only [hpdef] at this ⊢
        simpa using this
      rw [hnn, hpev]
      exact hε _ (by rw [Finset.mem_Icc]; omega)
    · have hk1 : 1 ≤ i.val - j.val := by omega
      have hk2 : i.val - j.val ≤ L := by have := i.isLt; omega
      have hsub : ((i.val - j.val : ℕ) : ℝ) = (i.val : ℝ) - (j.val : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hgt)]
      have hkey : ((i : ℝ) - (j : ℝ)) = (((i.val - j.val : ℕ)) : ℝ) := by
        rw [hcast, hsub]
      rw [hkey, hpev]
      exact hε _ (by rw [Finset.mem_Icc]; omega)
  have hoffbound :
      ‖∑ i : Fin (L + 1), ∑ j ∈ Finset.univ.erase i,
          v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ))‖
        ≤ ε * (((L : ℝ) + 1) * S) := by
    have hstep : ∀ i : Fin (L + 1),
        ‖∑ j ∈ Finset.univ.erase i,
            v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ))‖
          ≤ ∑ j ∈ Finset.univ.erase i, ε * (‖v i‖ * ‖v j‖) := by
      intro i
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => ?_)
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hnorm : ‖v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ))‖
          = ‖v i‖ * ‖v j‖ * ‖p ((i : ℝ) - (j : ℝ))‖ := by
        rw [norm_mul, norm_mul, Complex.norm_conj]
      rw [hnorm]
      have hb : ‖p ((i : ℝ) - (j : ℝ))‖ ≤ ε := hpair i j (Ne.symm hji)
      have h1 : 0 ≤ ‖v i‖ * ‖v j‖ := by positivity
      calc ‖v i‖ * ‖v j‖ * ‖p ((i : ℝ) - (j : ℝ))‖ ≤ ‖v i‖ * ‖v j‖ * ε :=
            mul_le_mul_of_nonneg_left hb h1
        _ = ε * (‖v i‖ * ‖v j‖) := by ring
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => hstep i) ?_
    have hmono : ∀ i : Fin (L + 1), (∑ j ∈ Finset.univ.erase i, ε * (‖v i‖ * ‖v j‖))
        ≤ ∑ j : Fin (L + 1), ε * (‖v i‖ * ‖v j‖) := by
      intro i
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ) ?_
      intro j _ _
      positivity
    refine le_trans (Finset.sum_le_sum fun i _ => hmono i) ?_
    have hT2' : (∑ i : Fin (L + 1), ∑ j : Fin (L + 1), ε * (‖v i‖ * ‖v j‖)) = ε * T ^ 2 := by
      rw [hT, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      simp only [Finset.mul_sum]
    rw [hT2']
    have : ε * T ^ 2 ≤ ε * (((L : ℝ) + 1) * S) := by
      refine mul_le_mul_of_nonneg_left ?_ hεnn
      nlinarith [hT2]
    exact this
  have hdiagval : (∑ i : Fin (L + 1), v i * (starRingEnd ℂ) (v i) * p 0)
      = ((S : ℝ) : ℂ) * (L : ℂ) := by
    rw [hp0, ← Finset.sum_mul, ← hSdef]
  have hoffnorm :
      ‖∑ i : Fin (L + 1), ∑ j ∈ Finset.univ.erase i,
          v i * (starRingEnd ℂ) (v j) * p ((i : ℝ) - (j : ℝ))‖ = (L : ℝ) * S := by
    rw [hoff, norm_neg, hdiagval, norm_mul]
    have h1 : ‖((S : ℝ) : ℂ)‖ = S := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hSnn]
    have h2 : ‖((L : ℕ) : ℂ)‖ = (L : ℝ) := by simp
    rw [h1, h2, mul_comm]
  have hLS : (0 : ℝ) < (L : ℝ) * S := by
    have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    positivity
  have hstep1 : (L : ℝ) * S ≤ ε * (((L : ℝ) + 1) * S) := by
    rw [← hoffnorm]
    exact hoffbound
  have hstep2 : (L : ℝ) ≤ ε * ((L : ℝ) + 1) := by
    have h2 : (L : ℝ) * S ≤ (ε * ((L : ℝ) + 1)) * S := by
      calc (L : ℝ) * S ≤ ε * (((L : ℝ) + 1) * S) := hstep1
        _ = (ε * ((L : ℝ) + 1)) * S := by ring
    exact le_of_mul_le_mul_right h2 hSpos
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hden : (0 : ℝ) < (L : ℝ) + 1 := by linarith
  have h3 : (L : ℝ) / ((L : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ hden]
    linarith
  have h4 : (1 : ℝ) / 2 ≤ (L : ℝ) / ((L : ℝ) + 1) := by
    rw [le_div_iff₀ hden]
    linarith
  linarith

/-- LEAF. The lower bound for the sums over the window: for `N ≥ 1` and every frequency cutoff
`H ≥ N - N/2` the weighted sum of the moduli of the exponential sums, with weights `1/(h+1)`, is at
least `1/(4N-2)`.  Its proof is the second moment `∑_{h ≤ N-N/2} ‖S h‖² ≥ N - N/2` (the kernel of
two distinct points is at least `-1`), so one frequency `h ≤ N - N/2 ≤ N` has `‖S h‖ ≥ 1`. -/
theorem leaf_dirichlet_lower (α γ : ℝ) (N H : ℕ) (hN : 1 ≤ N) (hH : N - N / 2 ≤ H) :
    1 ≤ (4 * (N : ℝ) - 2) * ∑ h ∈ Finset.Icc 1 H,
      ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  rcases eq_or_lt_of_le hN with hN1 | hN2
  · subst hN1
    have hH1 : 1 ≤ H := by omega
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 H := by simp [hH1]
    have hsingle : ∀ h : ℕ, ‖∑ n ∈ Finset.Ioc (1 / 2 : ℕ) 1, eC (h * α * F γ n)‖ = 1 := by
      intro h
      have hset : Finset.Ioc (1 / 2 : ℕ) 1 = ({1} : Finset ℕ) := by decide
      rw [hset, Finset.sum_singleton, norm_eC']
    have hone : (∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (1 / 2 : ℕ) 1, eC (h * α * F γ n)‖ / ((h : ℝ) + 1))
        = ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / ((h : ℝ) + 1) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hsingle]
    rw [hone]
    have hle := Finset.single_le_sum (f := fun h : ℕ => (1 : ℝ) / ((h : ℝ) + 1))
      (fun h _ => by positivity) hmem
    norm_num at hle ⊢
    linarith
  · have hN2' : 2 ≤ N := hN2
    set x : ℕ → ℝ := fun n => α * F γ n with hxdef
    set s : Finset ℕ := Finset.Ioc (N / 2) N with hsdef
    set L : ℕ := s.card with hLdef
    have hLeq : s.card = N - N / 2 := by rw [hsdef, Nat.card_Ioc]
    have hLpos : 1 ≤ L := by rw [hLdef, hLeq]; omega
    obtain ⟨h₀, hh₀mem, hh₀max⟩ := Finset.exists_max_image (Finset.Icc 1 L)
      (fun h => ‖∑ n ∈ s, eC (h * x n)‖) ⟨1, by simp [hLpos]⟩
    have hhalf := dirichlet_core L hLpos s hLdef.symm x _
      (fun h hh => hh₀max h hh)
    have hh₀1 : 1 ≤ h₀ := (Finset.mem_Icc.mp hh₀mem).1
    have hh₀L : h₀ ≤ L := (Finset.mem_Icc.mp hh₀mem).2
    have hsub : Finset.Icc 1 L ⊆ Finset.Icc 1 H := by
      intro h hh
      rw [Finset.mem_Icc] at *
      omega
    have hsumrewrite : ∀ h : ℕ, (∑ n ∈ s, eC (h * x n)) = ∑ n ∈ s, eC (h * α * F γ n) := by
      intro h
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hxdef]
      congr 1
      ring
    have hsumge : (1 : ℝ) / (2 * ((L : ℝ) + 1))
        ≤ ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ s, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
      have hnonneg : ∀ h ∈ Finset.Icc 1 H,
          (0 : ℝ) ≤ ‖∑ n ∈ s, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := fun h _ => by positivity
      refine le_trans ?_ (Finset.single_le_sum (f := fun h : ℕ =>
        ‖∑ n ∈ s, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)) hnonneg (hsub hh₀mem))
      rw [← hsumrewrite h₀]
      have hL₀ : (h₀ : ℝ) + 1 ≤ (L : ℝ) + 1 := by
        have : (h₀ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hh₀L
        linarith
      have hpos1 : (0 : ℝ) < (h₀ : ℝ) + 1 := by positivity
      have hstep : (1 : ℝ) / (2 * ((L : ℝ) + 1)) ≤ (1 : ℝ) / 2 / ((h₀ : ℝ) + 1) := by
        rw [div_div]
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      have hstep2 : (1 : ℝ) / 2 / ((h₀ : ℝ) + 1)
          ≤ ‖∑ n ∈ s, eC (h₀ * x n)‖ / ((h₀ : ℝ) + 1) :=
        div_le_div_of_nonneg_right hhalf (le_of_lt hpos1)
      linarith
    have hcardbound : N - N / 2 ≤ (N + 1) / 2 := by omega
    have hLb : 2 * ((L : ℝ) + 1) ≤ 4 * (N : ℝ) - 2 := by
      rw [hLdef, hLeq]
      have h1 : ((N - N / 2 : ℕ) : ℝ) ≤ (((N + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardbound
      have hdiv : 2 * (((N + 1) / 2 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
        have h3 : (N + 1) / 2 * 2 ≤ N + 1 := Nat.div_mul_le_self (N + 1) 2
        have h4 : (((N + 1) / 2 * 2 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast h3
        push_cast at h4
        linarith
      have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2'
      linarith
    have hcoefpos : (0 : ℝ) < 2 * ((L : ℝ) + 1) := by positivity
    have hone : (1 : ℝ) ≤ (4 * (N : ℝ) - 2) * (1 / (2 * ((L : ℝ) + 1))) := by
      rw [mul_one_div, le_div_iff₀ hcoefpos]
      linarith
    have hnonnegcoef : (0 : ℝ) ≤ 4 * (N : ℝ) - 2 := by
      have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2'
      linarith
    refine le_trans hone (mul_le_mul_of_nonneg_left ?_ hnonnegcoef)
    rw [hsdef] at hsumge ⊢
    exact hsumge

/-! ### Bookkeeping, proved -/

/-- The window `N/2 < n ≤ N` has `N - N/2` elements, which is `N/2` up to `1/2`. -/
private lemma card_window_shift (N : ℕ) :
    |((Finset.Ioc (N / 2) N).card : ℝ) - (N : ℝ) / 2| ≤ 1 / 2 := by
  rw [Nat.card_Ioc]
  have hdm : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
  have hsub : N - N / 2 = N / 2 + N % 2 := by omega
  have hN : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) := by
    have h : ((2 * (N / 2) + N % 2 : ℕ) : ℝ) = (N : ℝ) := by rw [hdm]
    push_cast at h ⊢
    linarith
  have hmod0 : ((N % 2 : ℕ) : ℝ) = 0 ∨ ((N % 2 : ℕ) : ℝ) = 1 := by
    have h2 : N % 2 = 0 ∨ N % 2 = 1 := by omega
    rcases h2 with h | h <;> rw [h] <;> norm_num
  rw [hsub]
  push_cast
  rw [abs_le]
  rcases hmod0 with h | h
  · rw [h] at hN
    norm_num at hN
    constructor <;> linarith
  · rw [h] at hN
    norm_num at hN
    constructor <;> linarith

/-- The polynomial part of the majorant, summed over a finite set of points, is bounded by the
exponential sums: `∑_n ∑_h (c h e(h x n)).re = ∑_h (c h ∑_n e(h x n)).re`, and each term of the
last sum is at most `‖c h‖ ‖∑_n e(h x n)‖`. -/
private lemma abs_sum_re_le (s : Finset ℕ) (H : ℕ) (c : ℕ → ℂ) (e : ℕ → ℕ → ℝ)
    (hbnd : ∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) :
    |∑ n ∈ s, ∑ h ∈ Finset.Icc 1 H, (c h * eC (e h n)).re| ≤
      2 * ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ s, eC (e h n)‖ / ((h : ℝ) + 1) := by
  classical
  have hswap : ∑ n ∈ s, ∑ h ∈ Finset.Icc 1 H, (c h * eC (e h n)).re
      = ∑ h ∈ Finset.Icc 1 H, (c h * ∑ n ∈ s, eC (e h n)).re := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    calc ∑ n ∈ s, (c h * eC (e h n)).re
        = ∑ n ∈ s, Complex.reCLM (c h * eC (e h n)) := by
            exact Finset.sum_congr rfl fun n _ => (Complex.reCLM_apply _).symm
      _ = Complex.reCLM (∑ n ∈ s, c h * eC (e h n)) :=
          (map_sum Complex.reCLM (fun n => c h * eC (e h n)) s).symm
      _ = Complex.reCLM (c h * ∑ n ∈ s, eC (e h n)) := by rw [Finset.mul_sum]
      _ = (c h * ∑ n ∈ s, eC (e h n)).re := Complex.reCLM_apply _
  have hterm : ∀ h ∈ Finset.Icc 1 H, |(c h * ∑ n ∈ s, eC (e h n)).re|
      ≤ 2 / ((h : ℝ) + 1) * ‖∑ n ∈ s, eC (e h n)‖ := by
    intro h hh
    calc |(c h * ∑ n ∈ s, eC (e h n)).re|
        ≤ ‖c h * ∑ n ∈ s, eC (e h n)‖ := Complex.abs_re_le_norm _
      _ = ‖c h‖ * ‖∑ n ∈ s, eC (e h n)‖ := norm_mul _ _
      _ ≤ 2 / ((h : ℝ) + 1) * ‖∑ n ∈ s, eC (e h n)‖ :=
          mul_le_mul_of_nonneg_right (hbnd h hh) (norm_nonneg _)
  rw [hswap]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
  rw [Finset.mul_sum]
  exact le_of_eq (Finset.sum_congr rfl fun h _ => by ring)

/-- Summing a per-point bound over the window: if at every point the indicator of the interval
differs from `b` plus the polynomial by at most `2/(H+1)`, then the count over the window differs
from `b` times its length by at most `2/(H+1)` times its length, plus the polynomial's total. -/
private lemma count_deviation (s : Finset ℕ) (H : ℕ) (b z₁ z₂ : ℝ) (x : ℕ → ℝ)
    (e : ℕ → ℕ → ℝ) (c : ℕ → ℂ) (he : ∀ h n, e h n = h * x n)
    (hpt : ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - b
      - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1)) :
    |((s.filter (fun n : ℕ => z₂ ≤ Int.fract (x n) ∧ Int.fract (x n) < z₁)).card : ℝ)
        - b * (s.card : ℝ) - ∑ n ∈ s, ∑ h ∈ Finset.Icc 1 H, (c h * eC (e h n)).re|
      ≤ 2 / ((H : ℝ) + 1) * (s.card : ℝ) := by
  classical
  simp only [he]
  have hcard : ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (x n) ∧ Int.fract (x n) < z₁)).card : ℝ)
      = ∑ n ∈ s, (if z₂ ≤ Int.fract (x n) ∧ Int.fract (x n) < z₁ then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hbc : b * (s.card : ℝ) = ∑ n ∈ s, b := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hcard, hbc]
  simp only [← Finset.sum_sub_distrib]
  have hsum : (∑ n ∈ s, 2 / ((H : ℝ) + 1)) = 2 / ((H : ℝ) + 1) * (s.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← hsum]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n _ => hpt (x n))

/-- The bookkeeping of the constants: the deviation of the count from `b N/2` is the deviation from
`b M`, the polynomial total, and the window shift, and these three fit inside `4N/(H+1) + 4N S`
once the shift is at most `1/2` and `1 ≤ 2N/(H+1) + (4N-2) S`. -/
private lemma arith_core (A b T S M N H' : ℝ) (hH' : 1 ≤ H') (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hMN : M ≤ N) (h1 : |A - b * M - T| ≤ 2 / H' * M) (h2 : |T| ≤ 2 * S)
    (h3 : |M - N / 2| ≤ 1 / 2) (h5 : 1 ≤ 2 * N / H' + (4 * N - 2) * S) :
    |A - b * N / 2| ≤ 4 * N / H' + 4 * N * S := by
  have hH'pos : (0 : ℝ) < H' := by linarith
  have hshift : b * M - b * N / 2 = b * (M - N / 2) := by ring
  have habs : |b * M - b * N / 2| = b * |M - N / 2| := by
    rw [hshift, abs_mul, abs_of_nonneg hb0]
  have hsplit : A - b * N / 2 = (A - b * M - T) + T + (b * M - b * N / 2) := by ring
  have h1a : |A - b * M - T| ≤ 2 * M / H' := by
    have he : 2 / H' * M = 2 * M / H' := by ring
    linarith
  have hMshift : 2 * M / H' ≤ 2 * N / H' := by
    refine div_le_div_of_nonneg_right ?_ hH'pos.le
    linarith
  have hb2 : b * (1 / 2) ≤ 1 / 2 := by linarith
  have hfour : 4 * N / H' = 2 * (2 * N / H') := by ring
  have h5a : (1 : ℝ) ≤ 2 * N / H' + (4 * N * S - 2 * S) := by
    have hprod : (4 * N - 2) * S = 4 * N * S - 2 * S := by ring
    rw [hprod] at h5
    linarith
  calc |A - b * N / 2|
      = |(A - b * M - T) + T + (b * M - b * N / 2)| := by rw [hsplit]
    _ ≤ |A - b * M - T| + |T| + |b * M - b * N / 2| := by
        have hA1 := abs_add_le ((A - b * M - T) + T) (b * M - b * N / 2)
        have hA2 := abs_add_le (A - b * M - T) T
        linarith
    _ = |A - b * M - T| + |T| + b * |M - N / 2| := by rw [habs]
    _ ≤ 2 * M / H' + 2 * S + b * (1 / 2) := by
        have hb' : b * |M - N / 2| ≤ b * (1 / 2) := mul_le_mul_of_nonneg_left h3 hb0
        linarith
    _ ≤ 2 * N / H' + 2 * S + 1 / 2 := by linarith
    _ ≤ 2 * N / H' + 2 * S + 1 := by linarith
    _ ≤ 4 * N / H' + 4 * N * S := by linarith

/-! ### Assembly -/

theorem leaf_fejer_majorant_split (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) - (z₁ - z₂) * N / 2| ≤ 4 * N / ((H : ℝ) + 1) + 4 * N * ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    simp
  have hb0 : (0 : ℝ) ≤ z₁ - z₂ := by linarith
  have hb1 : z₁ - z₂ ≤ 1 := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMN : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
    have h : (Finset.Ioc (N / 2) N).card ≤ N := by
      rw [Nat.card_Ioc]
      omega
    exact_mod_cast h
  obtain ⟨c, hcb, hcp⟩ := leaf_vaaler_trig_majorant H z₁ z₂ hz₂ hz1 hz₁
  have hT := abs_sum_re_le (Finset.Ioc (N / 2) N) H c
    (fun h n => h * α * F γ n) hcb
  have hA := count_deviation (Finset.Ioc (N / 2) N) H (z₁ - z₂) z₁ z₂
    (fun n => α * F γ n) (fun h n => h * α * F γ n) c
    (fun h n => by ring) hcp
  have hwin := card_window_shift N
  have habs : (1 : ℝ) ≤ 2 * (N : ℝ) / ((H : ℝ) + 1)
      + (4 * (N : ℝ) - 2) * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
    by_cases hc : (H : ℝ) + 1 ≤ 2 * (N : ℝ)
    · have hq : (1 : ℝ) ≤ 2 * (N : ℝ) / ((H : ℝ) + 1) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < (H : ℝ) + 1)]
        linarith
      have hsum0 : (0 : ℝ) ≤ ∑ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
        apply Finset.sum_nonneg
        intro h _
        positivity
      have hcoef0 : (0 : ℝ) ≤ 4 * (N : ℝ) - 2 := by linarith
      have : (0 : ℝ) ≤ (4 * (N : ℝ) - 2) * ∑ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) :=
        mul_nonneg hcoef0 hsum0
      linarith
    · have hbig : 2 * (N : ℝ) < (H : ℝ) + 1 := by linarith
      have hHge : N - N / 2 ≤ H := by
        have h2 : ((2 * N : ℕ) : ℝ) < ((H + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
        have h3 : 2 * N < H + 1 := by exact_mod_cast h2
        omega
      have hd := leaf_dirichlet_lower α γ N H hN hHge
      have hq : (0 : ℝ) ≤ 2 * (N : ℝ) / ((H : ℝ) + 1) := by positivity
      linarith
  exact arith_core _ (z₁ - z₂)
    (∑ n ∈ Finset.Ioc (N / 2) N, ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * α * F γ n)).re)
    (∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1))
    ((Finset.Ioc (N / 2) N).card : ℝ) (N : ℝ) ((H : ℝ) + 1)
    (by linarith) hb0 hb1 hMN hA hT hwin habs

end LeanLab.ExceptionalSet.U1539
