/-
Elementary reductions for the two oscillating small shift bands.
Gallagher 1975 p.127 display 2 supplies the arc width.
The fixed theta analytic remainder is a separate open task.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.Decomp495a

namespace LeanLab.Linnik.Decomp496a

open Filter MeasureTheory
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)

/-- Gallagher 1975 p.127 displays 1 and 2, specialized to the largest oscillating
phase range. For `θ ≤ 1/4` and `s ≤ θ`, every smaller range has the common saving `N ^ (-1/2)`. -/
theorem phase_character_oscillating_le {N q θ s d α a : ℝ} (hN : 1 ≤ N)
    (hq : 1 ≤ q) (hθ : θ ≤ 1 / 4) (hs : s ≤ θ)
    (hd : |d| ≤ N ^ s) (hα : |α - a / q| ≤ N ^ θ / (q * N)) :
    ‖LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * (a / q))‖ ≤ 2 * Real.pi * N ^ (-1 / 2 : ℝ) := by
  exact (Decomp495a.phase_character_le (by linarith) hq hd hα).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity))


/-- Gallagher 1975 p.127 display 2 and the lab mid band cut. A shift at most
`N ^ (3 * θ / 4)` gives phase exponent `7 * θ / 4 - 1`. At `θ ≤ 1/4`
this is at most `-9/16`, so this band also admits phase freezing. -/
theorem mid_band_phase_character_le {N q θ d α a : ℝ} (hN : 1 ≤ N)
    (hq : 1 ≤ q) (hθ : θ ≤ 1 / 4)
    (hd : |d| ≤ N ^ (3 * θ / 4))
    (hα : |α - a / q| ≤ N ^ θ / (q * N)) :
    ‖LeanLab.PNTPort.LargeSieve.e (d * α) -
      LeanLab.PNTPort.LargeSieve.e (d * (a / q))‖ ≤
      2 * Real.pi * N ^ (-9 / 16 : ℝ) := by
  exact (Decomp495a.phase_character_le (by linarith) hq hd hα).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity))


/-- Gallagher 1975 p.127 displays 1 and 2, at the normalization of p.138 display 5.
The logarithmic square cannot offset the uniform phase saving `N ^ (-1/2)`. -/
theorem logarithmic_phase_error_tendsto :
    Tendsto (fun N : ℕ => Real.pi * Real.log N ^ 2 / (N : ℝ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  simpa only [Real.rpow_two, mul_zero, Function.comp_def, mul_div_assoc] using
    (h.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul Real.pi


/-- Gallagher 1975 p.127 displays 1 and 2. Freeze the phase at any measurable
choice of rational arc centers. Parseval bounds the cost by the prime counting function
and the common `N ^ (-1/2)` phase saving. This does not approximate the frozen masses. -/
theorem oscillating_phase_freeze_le (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (hθ : θ ≤ 1 / 4)
    (d : ℝ) (hd : |d| ≤ (N : ℝ) ^ (θ)) (c : ℝ → ℝ) (hc : Measurable c)
    (hcenter : ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c α = (a : ℝ) / q ∧
          |α - c α| ≤ (N : ℝ) ^ θ / (q * N)) :
    |(∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e (d * α)).re) -
      (∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e (d * c α)).re)| ≤
      (2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ)) * Nat.primeCounting N := by
  have hw : IntegrableOn (fun α => ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2)
      (majorArcs N ((N : ℝ) ^ θ)) :=
    ((U7206.continuous_Sg N).norm.pow 2).integrableOn_Icc.mono_set
      (fun _ h => h.1)
  have hphase : ∀ᵐ α ∂volume.restrict (majorArcs N ((N : ℝ) ^ θ)),
      ‖LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * c α)‖ ≤ 2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ) := by
    filter_upwards [ae_restrict_mem (Decomp1532c.measurableSet_majorArcs N _)] with α hα
    obtain ⟨q, hq, _, a, _, _, hca, hwidth⟩ := hcenter α hα
    rw [hca] at hwidth ⊢
    exact phase_character_oscillating_le (by exact_mod_cast hN)
      (by exact_mod_cast hq) hθ le_rfl hd hwidth
  exact (Decomp495a.weighted_phase_freeze_le hw (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    c hc hphase).trans
      (mul_le_mul_of_nonneg_left (Decomp1532c.major_arc_Sg_mean_le N _) (by positivity))


/-- Gallagher 1975 p.127 displays 1 and 2 and p.138 tuple expansion. The local
phase freezing error summed over any of the two task bands is bounded by the full
number of exponent pairs times the single shift error. No singular series input is used. -/
theorem oscillating_filtered_freeze_le (k N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (hθ : θ ≤ 1 / 4)
    (T : Finset (Decomp1532a.pairs k (Nat.log 2 N)))
    (hd : ∀ x ∈ T, |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ))
    (c : ℝ → ℝ) (hc : Measurable c)
    (hcenter : ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c α = (a : ℝ) / q ∧
          |α - c α| ≤ (N : ℝ) ^ θ / (q * N)) :
    |(∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re) -
      (∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c α)).re)| ≤
      (Nat.log 2 N : ℝ) ^ (2 * k) *
        (2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ)) * Nat.primeCounting N := by
  classical
  let I := fun x : Decomp1532a.pairs k (Nat.log 2 N) =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re
  let F := fun x : Decomp1532a.pairs k (Nat.log 2 N) =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c α)).re
  let B : ℝ := (2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ)) * Nat.primeCounting N
  have hcard : (T.card : ℝ) ≤ (Nat.log 2 N : ℝ) ^ (2 * k) := by
    have h : T.card ≤ (Nat.log 2 N) ^ (2 * k) := by
      simpa [Decomp1532a.pairs, two_mul, pow_add] using Finset.card_le_univ T
    exact_mod_cast h
  change |T.sum I - T.sum F| ≤ _
  calc
    |T.sum I - T.sum F| = |∑ x ∈ T, (I x - F x)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x ∈ T, |I x - F x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ T, B := Finset.sum_le_sum (fun x hx =>
      oscillating_phase_freeze_le N hN θ hθ _ (hd x hx) c hc hcenter)
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (Nat.log 2 N : ℝ) ^ (2 * k) * B :=
      mul_le_mul_of_nonneg_right hcard (by dsimp [B]; positivity)
    _ = _ := by dsimp [B]; ring


/-- Gallagher 1975 p.127 displays 1 and 2, measured against the p.138 display 5
normalization. The phase freezing cost is eventually below any prescribed fraction
of `2 N / log squared N`, independently of theta and the number of exponent tuples. -/
theorem phase_freeze_budget_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ)) * Nat.primeCounting N ≤
        (2 * N / Real.log N ^ 2) * (δ / 24) := by
  have hev : ∀ᶠ N : ℕ in atTop,
      Real.pi * Real.log N ^ 2 / (N : ℝ) ^ (1 / 2 : ℝ) ≤ δ / 48 :=
    logarithmic_phase_error_tendsto.eventually
      (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 48))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨max N₀ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hp : (N : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hNp _).ne'
  have hpc : (Nat.primeCounting N : ℝ) ≤ 2 * N := by
    have hc : Nat.primeCounting N ≤ N + 1 := Nat.count_le Nat.Prime
    have hcr : (Nat.primeCounting N : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hc
    nlinarith
  have hsmall := hN₀ N (le_trans (le_max_left _ _) hN)
  calc
    (2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ)) * Nat.primeCounting N
      ≤ (2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ)) * (2 * N) := by gcongr
    _ = (2 * N / Real.log N ^ 2) *
        (2 * (Real.pi * Real.log N ^ 2 / (N : ℝ) ^ (1 / 2 : ℝ))) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hNp.le]
      field_simp
    _ ≤ (2 * N / Real.log N ^ 2) * (δ / 24) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)


/-- Gallagher 1975 p.127 display 2 and the p.138 tuple expansion normalization.
The total phase freezing error on any of the two oscillating bands is eventually
within its delta over 24 budget. The remaining analytic task is the frozen mass approximation. -/
theorem oscillating_filtered_freeze_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ, ∀ θ : ℝ, θ ≤ 1 / 4 →
      ∀ T : Finset (Decomp1532a.pairs k (Nat.log 2 N)),
      (∀ x ∈ T, |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ)) →
      ∀ c : ℝ → ℝ, Measurable c →
      (∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
        ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
          a ≤ q ∧ Nat.Coprime a q ∧ c α = (a : ℝ) / q ∧
            |α - c α| ≤ (N : ℝ) ^ θ / (q * N)) →
      |(∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re) -
        (∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c α)).re)| ≤
        (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 24) := by
  obtain ⟨N₁, hN₁⟩ := phase_freeze_budget_eventually δ hδ
  refine ⟨max N₁ 1, fun N hN k θ hθ T hd c hc hcenter => ?_⟩
  have hNpos : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hbudget := hN₁ N (le_trans (le_max_left _ _) hN)
  calc
    _ ≤ (Nat.log 2 N : ℝ) ^ (2 * k) *
        ((2 * Real.pi * (N : ℝ) ^ (-1 / 2 : ℝ)) * Nat.primeCounting N) := by
      simpa only [mul_assoc] using
        oscillating_filtered_freeze_le k N hNpos θ hθ T hd c hc hcenter
    _ ≤ (Nat.log 2 N : ℝ) ^ (2 * k) *
        ((2 * N / Real.log N ^ 2) * (δ / 24)) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by ring


/-- Gallagher 1975 p.127 displays 1 and 2 and the p.138 tuple expansion.
For every small shift filter, phase freezing preserves the little o remainder relative
to any chosen main term W. This is a reduction, not a proof of either remainder estimate. -/
theorem frozen_remainder_isLittleO_iff (k : ℕ) (θ : ℝ) (hθ : θ ≤ 1 / 4)
    (T : ∀ N : ℕ, Finset (Decomp1532a.pairs k (Nat.log 2 N)))
    (hd : ∀ N, ∀ x ∈ T N, |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ))
    (c : ℕ → ℝ → ℝ) (hc : ∀ N, Measurable (c N))
    (hcenter : ∀ N, ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c N α = (a : ℝ) / q ∧
          |α - c N α| ≤ (N : ℝ) ^ θ / (q * N)) (W : ℕ → ℝ) :
    let A : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re
    let F : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c N α)).re
    let M : ℕ → ℝ := fun N => 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
    Asymptotics.IsLittleO atTop (fun N => A N - W N) M ↔
      Asymptotics.IsLittleO atTop (fun N => F N - W N) M := by
  let A : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
    ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re
  let F : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
    ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c N α)).re
  let M : ℕ → ℝ := fun N => 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  change Asymptotics.IsLittleO atTop (fun N => A N - W N) M ↔
    Asymptotics.IsLittleO atTop (fun N => F N - W N) M
  have hphase : Asymptotics.IsLittleO atTop (fun N => A N - F N) M := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := oscillating_filtered_freeze_eventually (24 * ε) (by positivity)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hb := hN₀ N hN k θ hθ (T N) (hd N) (c N) (hc N) (hcenter N)
    rw [show 24 * ε / 24 = ε by ring] at hb
    change |A N - F N| ≤ M N * ε at hb
    have hM : 0 ≤ M N := by dsimp [M]; positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM]
    simpa only [mul_comm] using hb
  have hshift : Asymptotics.IsLittleO atTop
      (fun N => (A N - W N) - (F N - W N)) M :=
    hphase.congr_left (fun N => by ring)
  exact hshift.congr_of_sub


/-- CONDITIONAL ON the supplied frozen mass little o estimate. Gallagher 1975
p.127 display 2 and p.138 normalization. The proved phase reduction converts
that explicit input into the exact delta over twelve budget of either task band.
This does not assert the supplied analytic input or close either original leaf. -/
theorem oscillating_remainder_budget_of_frozen (k : ℕ) (θ : ℝ) (hθ : θ ≤ 1 / 4)
    (T : ∀ N : ℕ, Finset (Decomp1532a.pairs k (Nat.log 2 N)))
    (hd : ∀ N, ∀ x ∈ T N, |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ))
    (c : ℕ → ℝ → ℝ) (hc : ∀ N, Measurable (c N))
    (hcenter : ∀ N, ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c N α = (a : ℝ) / q ∧
          |α - c N α| ≤ (N : ℝ) ^ θ / (q * N)) (W : ℕ → ℝ)
    (hF : Asymptotics.IsLittleO atTop (fun N =>
      (∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c N α)).re) - W N)
      (fun N => 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re) - W N| ≤
        (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 12) := by
  have hA := (frozen_remainder_isLittleO_iff k θ hθ T hd c hc hcenter W).mpr hF
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hA.bound (div_pos hδ (by norm_num : (0 : ℝ) < 12)))
  refine ⟨N₀, fun N hN => ?_⟩
  have hM : 0 ≤ 2 * (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 :=
    by positivity
  have hb := hN₀ N hN
  simp only [Real.norm_eq_abs] at hb
  rw [abs_of_nonneg hM] at hb
  simpa only [mul_comm] using hb


/-- Gallagher 1975 p.127 display 2 and p.138 tuple expansion, applied to
the exact mid task filter. Measurable rational centers exist, and the
original singular series remainder is little o exactly when the frozen one is.
This isolates the analytic obligation and asserts neither remainder estimate. -/
theorem mid_band_frozen_reduction (k : ℕ) (θ : ℝ) (hθ : θ ≤ 1 / 4) :
    ∃ c : ℕ → ℝ → ℝ, (∀ N, Measurable (c N)) ∧
    (∀ N, ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c N α = (a : ℝ) / q ∧
          |α - c N α| ≤ (N : ℝ) ^ θ / (q * N)) ∧
    (let T : ∀ N : ℕ, Finset (Decomp1532a.pairs k (Nat.log 2 N)) := fun N =>
      Finset.univ.filter (fun x => Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ);
    let W : ℕ → ℝ := fun N => ∑ x ∈ T N,
      Decomp1532b.Jn N (Decomp1532a.dif x) *
        (Decomp1532b.singSeries (Decomp1532a.dif x)).re;
    let M : ℕ → ℝ := fun N => 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
    Asymptotics.IsLittleO atTop (fun N =>
      (∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re) - W N) M ↔
    Asymptotics.IsLittleO atTop (fun N =>
      (∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c N α)).re) - W N) M) := by
  classical
  choose c hc hcenter using fun N : ℕ =>
    Decomp495a.exists_measurable_arc_center N ((N : ℝ) ^ θ)
  refine ⟨c, hc, hcenter, ?_⟩
  let T : ∀ N : ℕ, Finset (Decomp1532a.pairs k (Nat.log 2 N)) := fun N =>
      Finset.univ.filter (fun x => Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ)
  let W : ℕ → ℝ := fun N => ∑ x ∈ T N,
      Decomp1532b.Jn N (Decomp1532a.dif x) *
        (Decomp1532b.singSeries (Decomp1532a.dif x)).re
  apply frozen_remainder_isLittleO_iff k θ hθ T ?_ c hc hcenter W
  intro N x hx
  exact (Finset.mem_filter.mp hx).2.2.2.2


/-- Gallagher 1975 p.127 display 2 and p.138 tuple expansion, applied to
the exact top task filter. Measurable rational centers exist, and the
original singular series remainder is little o exactly when the frozen one is.
This isolates the analytic obligation and asserts neither remainder estimate. -/
theorem top_band_frozen_reduction (k : ℕ) (θ : ℝ) (hθ : θ ≤ 1 / 4) :
    ∃ c : ℕ → ℝ → ℝ, (∀ N, Measurable (c N)) ∧
    (∀ N, ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c N α = (a : ℝ) / q ∧
          |α - c N α| ≤ (N : ℝ) ^ θ / (q * N)) ∧
    (let T : ∀ N : ℕ, Finset (Decomp1532a.pairs k (Nat.log 2 N)) := fun N =>
      Finset.univ.filter (fun x => Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ);
    let W : ℕ → ℝ := fun N => ∑ x ∈ T N,
      Decomp1532b.Jn N (Decomp1532a.dif x) *
        (Decomp1532b.singSeries (Decomp1532a.dif x)).re;
    let M : ℕ → ℝ := fun N => 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
    Asymptotics.IsLittleO atTop (fun N =>
      (∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re) - W N) M ↔
    Asymptotics.IsLittleO atTop (fun N =>
      (∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c N α)).re) - W N) M) := by
  classical
  choose c hc hcenter using fun N : ℕ =>
    Decomp495a.exists_measurable_arc_center N ((N : ℝ) ^ θ)
  refine ⟨c, hc, hcenter, ?_⟩
  let T : ∀ N : ℕ, Finset (Decomp1532a.pairs k (Nat.log 2 N)) := fun N =>
      Finset.univ.filter (fun x => Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * θ / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ)
  let W : ℕ → ℝ := fun N => ∑ x ∈ T N,
      Decomp1532b.Jn N (Decomp1532a.dif x) *
        (Decomp1532b.singSeries (Decomp1532a.dif x)).re
  apply frozen_remainder_isLittleO_iff k θ hθ T ?_ c hc hcenter W
  intro N x hx
  exact (Finset.mem_filter.mp hx).2.2.2.2


/-- Gallagher 1975 p.134 display 3. A translated exponent box gives many
nonzero shifts between explicit lower and upper powers of two. This lets us
check strict lower cuts as well as the upper cuts of the two task bands. -/
theorem shifted_box_embedding (m t L : ℕ) (hmt : m ≤ t) (hL : t + m ≤ L) :
    ∃ f : Decomp1532a.pairs 2 m → Decomp1532a.pairs 2 L,
      Function.Injective f ∧ ∀ x,
        (2 : ℤ) ^ (t + 1) ≤ Decomp1532a.dif (f x) ∧
        Decomp1532a.dif (f x) ≤ (2 : ℤ) ^ (t + m + 1) := by
  let f : Decomp1532a.pairs 2 m → Decomp1532a.pairs 2 L := fun x =>
    ((fun i => ⟨(x.1 i : ℕ) + t, by have h := (x.1 i).isLt; omega⟩),
      fun i => ⟨(x.2 i : ℕ), by have h := (x.2 i).isLt; omega⟩)
  refine ⟨f, ?_, ?_⟩
  · intro x y h
    apply Prod.ext
    · funext i
      apply Fin.ext
      have hi := congrArg (fun z : Decomp1532a.pairs 2 L => (z.1 i : ℕ)) h
      dsimp [f] at hi
      omega
    · funext i
      apply Fin.ext
      exact congrArg (fun z : Decomp1532a.pairs 2 L => (z.2 i : ℕ)) h
  · intro x
    have hsecond : U1434Lemma21.sv (f x).2 ≤ 2 * 2 ^ t := by
      have hs : U1434Lemma21.sv (f x).2 = U1434Lemma21.sv x.2 := rfl
      rw [hs]
      exact (U1434Lemma21.sv_le x.2).trans
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hmt))
    have hfirst_low : 2 * 2 ^ (t + 1) ≤ U1434Lemma21.sv (f x).1 := by
      change 2 * 2 ^ (t + 1) ≤ ∑ i : Fin 2, 2 ^ ((x.1 i : ℕ) + t + 1)
      calc
        _ = ∑ _i : Fin 2, 2 ^ (t + 1) := by simp [two_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ =>
          Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfirst_up : U1434Lemma21.sv (f x).1 ≤ 2 * 2 ^ (t + m) := by
      change (∑ i : Fin 2, 2 ^ ((x.1 i : ℕ) + t + 1)) ≤ 2 * 2 ^ (t + m)
      calc
        _ ≤ ∑ _i : Fin 2, 2 ^ (t + m) := Finset.sum_le_sum fun i _ =>
          Nat.pow_le_pow_right (by norm_num) (by have h := (x.1 i).isLt; omega)
        _ = _ := by simp [two_mul]
    have hsl : (U1434Lemma21.sv (f x).2 : ℤ) ≤ 2 * (2 : ℤ) ^ t := by
      exact_mod_cast hsecond
    have hfl : 2 * (2 : ℤ) ^ (t + 1) ≤ (U1434Lemma21.sv (f x).1 : ℤ) := by
      exact_mod_cast hfirst_low
    have hfu : (U1434Lemma21.sv (f x).1 : ℤ) ≤ 2 * (2 : ℤ) ^ (t + m) := by
      exact_mod_cast hfirst_up
    constructor
    · dsimp [Decomp1532a.dif]
      rw [pow_succ] at hfl ⊢
      linarith
    · dsimp [Decomp1532a.dif]
      rw [pow_succ]
      have hsn : (0 : ℤ) ≤ U1434Lemma21.sv (f x).2 := Nat.cast_nonneg _
      linarith


/-- Gallagher 1975 p.134 display 3 and the two lab band cuts. At theta equal
to one quarter and k equal to two, each band contains at least one over 64 to
four of all tuples along N equal to two to 64m. The parameter b is zero for
the mid band and one for the top band. This concerns counts, not prime errors. -/
theorem band_box_density (m b : ℕ) (hm : 1 ≤ m) (hb : b ≤ 1) :
    let L : ℕ := 64 * m
    let N : ℕ := 2 ^ L
    let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
      ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
      ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 16) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    m ^ 4 ≤ T.card ∧ L ^ 4 ≤ 64 ^ 4 * T.card := by
  classical
  let L : ℕ := 64 * m
  let N : ℕ := 2 ^ L
  let t : ℕ := (10 + 4 * b) * m
  let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
    Decomp1532a.dif x ≠ 0 ∧
    ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
    ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 16) ∧
    |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) ∧
    |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
  change m ^ 4 ≤ T.card ∧ L ^ 4 ≤ 64 ^ 4 * T.card
  have hb' : b = 0 ∨ b = 1 := by omega
  have hmt : m ≤ t := by rcases hb' with rfl | rfl <;> dsimp [t] <;> omega
  have htL : t + m ≤ L := by rcases hb' with rfl | rfl <;> dsimp [t, L] <;> omega
  obtain ⟨f, hf, hbox⟩ := shifted_box_embedding m t L hmt htL
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (Nat.one_le_pow L 2 (by norm_num))
  have hcut (r : ℝ) : (N : ℝ) ^ r = (2 : ℝ) ^ ((L : ℝ) * r) := by
    simp only [N, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hmaps : Set.MapsTo f (Finset.univ : Finset (Decomp1532a.pairs 2 m)) T := by
    intro x _hx
    have hlo : (2 : ℝ) ^ (t + 1) ≤ (Decomp1532a.dif (f x) : ℝ) := by
      exact_mod_cast (hbox x).1
    have hhi : (Decomp1532a.dif (f x) : ℝ) ≤ (2 : ℝ) ^ (t + m + 1) := by
      exact_mod_cast (hbox x).2
    have hp : (0 : ℝ) < Decomp1532a.dif (f x) :=
      (pow_pos (by norm_num) _).trans_le hlo
    have hlow : (N : ℝ) ^ ((2 + b : ℝ) / 16) < |(Decomp1532a.dif (f x) : ℝ)| := by
      rw [abs_of_pos hp, hcut]
      apply lt_of_lt_of_le _ hlo
      rw [← Real.rpow_natCast]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      rcases hb' with rfl | rfl <;> dsimp [L, t] <;> push_cast <;> nlinarith
    have hupp : |(Decomp1532a.dif (f x) : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) := by
      rw [abs_of_pos hp, hcut]
      apply hhi.trans
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rcases hb' with rfl | rfl <;> dsimp [L, t] <;> push_cast <;> nlinarith
    have hglobal : |(Decomp1532a.dif (f x) : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      apply hupp.trans
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have hbr : (b : ℝ) ≤ 1 := by exact_mod_cast hb
      linarith
    have hsmall : (N : ℝ) ^ (1 / 8 : ℝ) < |(Decomp1532a.dif (f x) : ℝ)| := by
      apply lt_of_le_of_lt _ hlow
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have hbr : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by exact_mod_cast hp.ne',
      not_le.mpr hsmall, not_le.mpr hlow, hupp, hglobal⟩
  have hcard : m ^ 4 ≤ T.card := by
    have h := Finset.card_le_card_of_injOn f hmaps hf.injOn
    simpa [Decomp1532a.pairs, ← pow_add] using h
  refine ⟨hcard, ?_⟩
  calc
    L ^ 4 = 64 ^ 4 * m ^ 4 := mul_pow _ _ _
    _ ≤ 64 ^ 4 * T.card := Nat.mul_le_mul_left _ hcard


/-- Gallagher 1975 p.134 display 3 and the two lab band cuts. For either
band the tuple count is not little o of the full tuple count. This rules out
a proof by tuple sparsity alone and does not refute the prime correlation leaf. -/
theorem band_count_not_littleO (b : ℕ) (hb : b ≤ 1) :
    let R : ℕ → ℝ := fun N =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 16) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
    ¬ Asymptotics.IsLittleO atTop R (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  let R : ℕ → ℝ := fun N =>
    (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 16) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
  change ¬ Asymptotics.IsLittleO atTop R (fun N => (Nat.log 2 N : ℝ) ^ 4)
  intro h
  let ε : ℝ := 1 / (2 * 64 ^ 4)
  obtain ⟨Nk, hNk⟩ := eventually_atTop.mp (h.bound (by dsimp [ε]; positivity : 0 < ε))
  let m := max Nk 1
  let L := 64 * m
  let N : ℕ := 2 ^ L
  let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
    Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 16) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
  have hm : 1 ≤ m := le_max_right _ _
  have hmNk : Nk ≤ m := le_max_left _ _
  have hmL : m ≤ L := by dsimp [L]; omega
  have hNL : L < N := L.lt_two_pow_self
  have hNNk : Nk ≤ N := by omega
  have hlog : Nat.log 2 N = L := by
    dsimp [N]
    exact Nat.log_pow (by norm_num) L
  have hR : R N = (T.card : ℝ) := by
    dsimp [R]
    rw [hlog]
  have hdensity : L ^ 4 ≤ 64 ^ 4 * T.card := (band_box_density m b hm hb).2
  have hd : (L : ℝ) ^ 4 ≤ (64 : ℝ) ^ 4 * (T.card : ℝ) := by exact_mod_cast hdensity
  have hb : (T.card : ℝ) ≤ ε * (L : ℝ) ^ 4 := by
    have hh := hNk N hNNk
    rw [hR, hlog, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)] at hh
    exact hh
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpos : (0 : ℝ) < (L : ℝ) ^ 4 := pow_pos hLp _
  have hcoeff : (64 : ℝ) ^ 4 * ε = 1 / 2 := by norm_num [ε]
  have hbd : (64 : ℝ) ^ 4 * (T.card : ℝ) ≤ (1 / 2 : ℝ) * (L : ℝ) ^ 4 := by
    calc
      _ ≤ (64 : ℝ) ^ 4 * (ε * (L : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [← mul_assoc, hcoeff]
  have hf := hd.trans hbd
  linarith only [hf, hpos]


/-- Gallagher 1975 p.134 display 3 and the exact task filters. Neither original
band has little o tuple count at `θ = 1/4` and `k = 2`. This specializes the
translated box obstruction without replacing any original filter clause. -/
theorem original_band_counts_not_littleO :
    (¬ Asymptotics.IsLittleO atTop (fun N : ℕ =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * (1 / 4 : ℝ) / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ))
      (fun N => (Nat.log 2 N : ℝ) ^ 4)) ∧
    (¬ Asymptotics.IsLittleO atTop (fun N : ℕ =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * (1 / 4 : ℝ) / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ))
      (fun N => (Nat.log 2 N : ℝ) ^ 4)) := by
  have h₀ := band_count_not_littleO 0 (by norm_num)
  have h₁ := band_count_not_littleO 1 (by norm_num)
  constructor
  · norm_num at h₀ ⊢
    simpa only [and_self_left] using h₀
  · norm_num at h₁ ⊢
    simpa only [and_self] using h₁


/-- Gallagher 1975 p.127 Theorem 3 and p.138 error sum. The arithmetic
weight `abs(n) / phi(abs(n))` is at least one on every nonzero shift.
Thus the weighted tuple count on either task band is not little o of the
full tuple count either. This is a bound obstruction, not a prime error lower bound. -/
theorem band_weight_not_littleO (b : ℕ) (hb : b ≤ 1) :
    let W : ℕ → ℝ := fun N =>
      ∑ x : Decomp1532a.pairs 2 (Nat.log 2 N) with
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 16) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ),
        Decomp466a.totientWeight (Decomp1532a.dif x)
    ¬ Asymptotics.IsLittleO atTop W (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  let T : ∀ N : ℕ, Finset (Decomp1532a.pairs 2 (Nat.log 2 N)) := fun N =>
    Finset.univ.filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 16) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((3 + b : ℝ) / 16) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
  let W : ℕ → ℝ := fun N =>
    ∑ x ∈ T N, Decomp466a.totientWeight (Decomp1532a.dif x)
  change ¬ Asymptotics.IsLittleO atTop W (fun N => (Nat.log 2 N : ℝ) ^ 4)
  intro hW
  apply band_count_not_littleO b hb
  change Asymptotics.IsLittleO atTop (fun N => ((T N).card : ℝ))
    (fun N => (Nat.log 2 N : ℝ) ^ 4)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hW.bound hε] with N hN
  have hcard : ((T N).card : ℝ) ≤ W N := by
    calc
      _ = ∑ _x ∈ T N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx =>
        MajorArcEnergy.one_le_totientWeight (Finset.mem_filter.mp hx).2.1)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hcard.trans ((le_abs_self _).trans hN)


/-- Gallagher 1975 p.134 display 3 and the lab band cuts. At `k = 2`,
`θ = 1/4` and `N = 2 ^ 32`, the exact two original filters contain shifts
32 and 128. Thus neither strict lower cut makes its target vacuous. -/
theorem two_original_filters_nonempty :
    let Q : ℝ → ℝ := fun r => ((2 ^ 32 : ℕ) : ℝ) ^ r
    ∃ x₁ x₂ : Decomp1532a.pairs 2 (Nat.log 2 (2 ^ 32)),
      (Decomp1532a.dif x₁ ≠ 0 ∧
        ¬ |(Decomp1532a.dif x₁ : ℝ)| ≤ Q ((1 / 4 : ℝ) / 2) ∧
        |(Decomp1532a.dif x₁ : ℝ)| ≤ Q (3 * (1 / 4 : ℝ) / 4) ∧
        |(Decomp1532a.dif x₁ : ℝ)| ≤ Q (1 / 4)) ∧
      (Decomp1532a.dif x₂ ≠ 0 ∧
        ¬ |(Decomp1532a.dif x₂ : ℝ)| ≤ Q ((1 / 4 : ℝ) / 2) ∧
        ¬ |(Decomp1532a.dif x₂ : ℝ)| ≤ Q (3 * (1 / 4 : ℝ) / 4) ∧
        |(Decomp1532a.dif x₂ : ℝ)| ≤ Q (1 / 4)) := by
  dsimp only
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))]
  let x₁ : Decomp1532a.pairs 2 32 := (![4, 1], ![0, 0])
  let x₂ : Decomp1532a.pairs 2 32 := (![6, 1], ![0, 0])
  have hd₁ : Decomp1532a.dif x₁ = 32 := by
    norm_num [x₁, Decomp1532a.dif, U1434Lemma21.sv, Fin.sum_univ_two]
  have hd₂ : Decomp1532a.dif x₂ = 128 := by
    norm_num [x₂, Decomp1532a.dif, U1434Lemma21.sv, Fin.sum_univ_two]
  have hp (r : ℝ) : ((2 ^ 32 : ℕ) : ℝ) ^ r = (2 : ℝ) ^ ((32 : ℝ) * r) := by
    rw [Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 32 r]
    norm_num
  have h₁ : ((2 ^ 32 : ℕ) : ℝ) ^ ((1 / 4 : ℝ) / 2) = 16 := by
    rw [hp]; norm_num
  have h₂ : ((2 ^ 32 : ℕ) : ℝ) ^ (3 * (1 / 4 : ℝ) / 4) = 64 := by
    rw [hp]; norm_num [show (2 : ℝ) ^ (6 : ℝ) = 64 by norm_num]
  have h₃ : ((2 ^ 32 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = 256 := by
    rw [hp]; norm_num [show (2 : ℝ) ^ (8 : ℝ) = 256 by norm_num]
  refine ⟨x₁, x₂, ?_⟩
  norm_num [hd₁, hd₂, h₁, h₂, h₃]


end LeanLab.Linnik.Decomp496a

#print axioms LeanLab.Linnik.Decomp496a.phase_character_oscillating_le

#print axioms LeanLab.Linnik.Decomp496a.mid_band_phase_character_le

#print axioms LeanLab.Linnik.Decomp496a.logarithmic_phase_error_tendsto

#print axioms LeanLab.Linnik.Decomp496a.oscillating_phase_freeze_le

#print axioms LeanLab.Linnik.Decomp496a.oscillating_filtered_freeze_le

#print axioms LeanLab.Linnik.Decomp496a.phase_freeze_budget_eventually

#print axioms LeanLab.Linnik.Decomp496a.oscillating_filtered_freeze_eventually

#print axioms LeanLab.Linnik.Decomp496a.frozen_remainder_isLittleO_iff

#print axioms LeanLab.Linnik.Decomp496a.oscillating_remainder_budget_of_frozen

#print axioms LeanLab.Linnik.Decomp496a.mid_band_frozen_reduction

#print axioms LeanLab.Linnik.Decomp496a.top_band_frozen_reduction

#print axioms LeanLab.Linnik.Decomp496a.shifted_box_embedding

#print axioms LeanLab.Linnik.Decomp496a.band_box_density

#print axioms LeanLab.Linnik.Decomp496a.band_count_not_littleO

#print axioms LeanLab.Linnik.Decomp496a.original_band_counts_not_littleO

#print axioms LeanLab.Linnik.Decomp496a.band_weight_not_littleO

#print axioms LeanLab.Linnik.Decomp496a.two_original_filters_nonempty
