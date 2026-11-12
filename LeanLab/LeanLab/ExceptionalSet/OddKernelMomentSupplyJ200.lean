import Mathlib
import LeanLab.ExceptionalSet.KernelMomentSupplyJ200
import LeanLab.ExceptionalSet.LargePhiSupplyJ200
import LeanLab.ExceptionalSet.LEAF_lemma9_odd

/-!
Sorry-free supply for the odd kernel moment of P0082 page 369, display (30), the cognate of
display (29) with `w_o(α) = w_e(-α)`, the kernel `K_o(α) = K_e(-α)` and the index set
`𝒩_o = {N/2 < n ≤ N : ν_n odd}`.
Source: P0082, J. Bruedern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378.

The key reduction: `|S(α)² K_o(α)| = |S(-α)² K_e(-α)| = |S(α)² K_e(α)|`, because `S(-α)` is the
conjugate of `S(α)` and `|K_e|` is even. So the tail removal and the absolute Gram integral of
the odd moment are those of the even moment with `Φ_o` in place of `Φ_e`, and the generic
machinery of `KernelMomentSupplyJ200` applies after one rewrite. The large `Φ_o` part is the
proof of `LargePhiSupplyJ200.even_gram_large_of_lemma9` with `Φ_o` and the odd Lemma 9, taken
here as the explicit hypothesis `h9 : Lemma9Odd.Lemma9odd`.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.OddKernelMomentSupplyJ200

open Real MeasureTheory Set Filter ComplexConjugate
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun eC majorArcs calE nu)
open LeanLab.ExceptionalSet.OddKernel467 (evenKernel)
open LeanLab.ExceptionalSet.EvenMinorSupplyJ200 (oddKernel)
open LeanLab.ExceptionalSet.Lemma9Odd (Phio Lemma9odd)
open LeanLab.ExceptionalSet.KernelMomentSupplyJ200 (integrand total_integrable)

/-- `|S(α)² K_o(α)| = |S(α)² K_e(α)|`: `S(-α) = conj S(α)` and `|K_e|` is even, P0082 page 369
after (39). -/
theorem norm_odd_eq_even (P X Δ α : ℝ) :
    ‖Sp P X α ^ 2 * oddKernel Δ α‖ = ‖Sp P X α ^ 2 * evenKernel Δ α‖ := by
  have he (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
  have hs : Sp P X (-α) = conj (Sp P X α) := by
    simp only [Sp, map_sum, map_mul, Complex.conj_ofReal, he, neg_mul]
  have h := KernelMomentSupplyJ200.norm_integrand_neg P X Δ 0 α
  simp only [integrand, mul_zero, neg_zero, norm_mul, norm_pow, U1539.norm_eC, mul_one] at h
  rw [hs, Complex.norm_conj] at h
  simp only [oddKernel, norm_mul, norm_pow]
  exact h

/-- The odd kernel integrand `S(α)² K_o(α) e(-α v)` of display (30). -/
noncomputable def integrandO (P X Δ v α : ℝ) : ℂ :=
  Sp P X α ^ 2 * oddKernel Δ α * eC (-(α * v))

/-- The odd integrand has the norm of the even one. -/
theorem norm_integrandO (P X Δ v α : ℝ) :
    ‖integrandO P X Δ v α‖ = ‖integrand P X Δ v α‖ := by
  simp only [integrandO, integrand, norm_mul (Sp P X α ^ 2 * oddKernel Δ α),
    norm_mul (Sp P X α ^ 2 * evenKernel Δ α), norm_odd_eq_even]

/-- The odd integrand is integrable. -/
theorem integrandO_integrable (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (integrandO P X Δ v) := by
  have hc : Continuous (integrandO P X Δ v) := by
    have h1 : Continuous (fun α : ℝ => Sp P X α ^ 2 * eC (-(α * v))) := by
      unfold Sp eC; fun_prop
    have h2 := (EvenMinorSupplyJ200.oddKernel_continuous Δ)
    have : integrandO P X Δ v = fun α => (Sp P X α ^ 2 * eC (-(α * v))) * oddKernel Δ α := by
      funext α; simp only [integrandO]; ring
    rw [this]; exact h1.mul h2
  refine (total_integrable P X Δ v hΔ hΔ1).norm.mono' hc.aestronglyMeasurable
    (Eventually.of_forall (fun α => ?_))
  rw [norm_integrandO]

/-- The tail removal after display (34) for the odd integrand. -/
theorem truncation_error_le_odd (P X Δ v T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 4 ≤ T) (M : Set ℝ) :
    ‖(∫ α in M, integrandO P X Δ v α) -
        (∫ α in M ∩ Icc (-T) T, integrandO P X Δ v α)‖ ≤
      8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T) := by
  have hf : Integrable (integrandO P X Δ v) := integrandO_integrable P X Δ v hΔ hΔ1
  have he := integral_inter_add_sdiff (t := Icc (-T) T) measurableSet_Icc
    (show IntegrableOn (integrandO P X Δ v) M from hf.integrableOn)
  have hd : (∫ α in M, integrandO P X Δ v α) -
      (∫ α in M ∩ Icc (-T) T, integrandO P X Δ v α) =
      ∫ α in M \ Icc (-T) T, integrandO P X Δ v α := by
    rw [← he]; abel
  rw [hd]
  have hn : (fun α => ‖integrandO P X Δ v α‖) = fun α => ‖integrand P X Δ v α‖ := by
    funext α; exact norm_integrandO P X Δ v α
  refine (norm_integral_le_integral_norm _).trans (le_trans ?_
    (KernelMomentSupplyJ200.outside_real_tail_le P X Δ v T hX hΔ hΔ1 hT))
  rw [hn]
  exact setIntegral_mono_set (total_integrable P X Δ v hΔ hΔ1).norm.integrableOn
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show M \ Icc (-T) T ⊆ (Icc (-T) T)ᶜ from fun _ h => h.2).eventuallySubset

/-- The Gram kernel of the squaring (37) for the odd integrand, with the even absolute
weights by `norm_odd_eq_even`. -/
theorem norm_gram_sum_odd (P X Δ : ℝ) (s : Finset ℕ) (v : ℕ → ℝ) (α β : ℝ) :
    ‖∑ n ∈ s, integrandO P X Δ (v n) α * conj (integrandO P X Δ (v n) β)‖ =
      ‖Sp P X α ^ 2 * evenKernel Δ α‖ * ‖Sp P X β ^ 2 * evenKernel Δ β‖ *
        ‖∑ n ∈ s, eC ((β - α) * v n)‖ := by
  have he (n : ℕ) : integrandO P X Δ (v n) α * conj (integrandO P X Δ (v n) β) =
      (Sp P X α ^ 2 * oddKernel Δ α) * conj (Sp P X β ^ 2 * oddKernel Δ β) *
        eC ((β - α) * v n) := by
    have hc (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
    simp only [integrandO, map_mul, hc]
    have h2 : eC (-(α * v n)) * eC (-(-(β * v n))) = eC ((β - α) * v n) := by
      rw [KernelMomentSupplyJ200.eC_mul_eC]; congr 1; ring
    rw [← h2]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul, norm_mul, Complex.norm_conj, norm_odd_eq_even,
    norm_odd_eq_even]

/-- P0082 page 369 after (39), the tail removal and the squaring for the odd integrand, with
the right side of `KernelMomentSupplyJ200.moment_tail_gram`: the even absolute weights. -/
theorem moment_tail_gram_odd (P X Δ T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 4 ≤ T) (M : Set ℝ) (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, ‖∫ α in M, integrandO P X Δ (v n) α‖ ^ 2) ≤
      2 * (∫ z : ℝ × ℝ, ‖Sp P X z.1 ^ 2 * evenKernel Δ z.1‖ *
          ‖Sp P X z.2 ^ 2 * evenKernel Δ z.2‖ * ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖
          ∂(volume.restrict (M ∩ Icc (-T) T)).prod (volume.restrict (M ∩ Icc (-T) T))) +
        2 * s.card * (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 := by
  set τ := 8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)
  set A := M ∩ Icc (-T) T
  have hterm (n : ℕ) : ‖∫ α in M, integrandO P X Δ (v n) α‖ ^ 2 ≤
      2 * ‖∫ α in A, integrandO P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2 :=
    KernelMomentSupplyJ200.norm_sq_le_of_sub _ _ τ
      (truncation_error_le_odd P X Δ (v n) T hX hΔ hΔ1 hT M)
  have hg := KernelMomentSupplyJ200.moment_le_absolute_gram s A
    (fun n => integrandO P X Δ (v n))
    (fun n _ => (integrandO_integrable P X Δ (v n) hΔ hΔ1).integrableOn)
  simp_rw [norm_gram_sum_odd] at hg
  calc (∑ n ∈ s, ‖∫ α in M, integrandO P X Δ (v n) α‖ ^ 2)
      ≤ ∑ n ∈ s, (2 * ‖∫ α in A, integrandO P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2) :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = 2 * (∑ n ∈ s, ‖∫ α in A, integrandO P X Δ (v n) α‖ ^ 2) + 2 * s.card * τ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := by gcongr

open LeanLab.ExceptionalSet.LargePhiSupplyJ200
open LeanLab.ExceptionalSet.KernelMomentSupplyJ200

set_option maxHeartbeats 800000 in
/-- P0082 page 369, the large `Φ_o` part for display (30), from the odd Lemma 9 and display (39),
CONDITIONAL ON the odd Lemma 9 as the hypothesis `h9`. The proof of
`LargePhiSupplyJ200.even_gram_large_of_lemma9` with `Φ_o` in place of `Φ_e`: for
`δ < min(δ₉, 1/30)` and `κ ≤ κ₉/4` the pairs with `|Φ_o(β - α)| > N ℰ(2κ)^{-2/3}` have
`|β - α| ≤ 2ℰ ≤ X^δ` and pass the threshold, so `β` lies within `X^{δ-1}` of some `α + h/2`,
`|h| ≤ ℰ(κ₉)^{2/3}`; on the minor arcs `|S(β)| ≤ 14404 X^{1-3δ} (log X)^4`, `|K_e| ≤ 1` and
`|Φ_o| ≤ N`. The weights are the even ones, equal to the odd ones by `norm_odd_eq_even`. -/
theorem odd_gram_large_of_lemma9odd (h9 : Lemma9odd) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∫ z : ℝ × ℝ,
            {z : ℝ × ℝ | (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) <
                ‖Phio γ N (z.2 - z.1)‖}.indicator (fun z : ℝ × ℝ =>
              ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.1 ^ 2 *
                  evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.1‖ *
                ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.2 ^ 2 *
                  evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.2‖ *
                ‖Phio γ N (z.2 - z.1)‖) z
            ∂(volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N))).prod
              (volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N)))) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ9, hδ9, h9'⟩ := h9 γ h1 h2
  refine ⟨min δ9 (1 / 30), lt_min hδ9 (by norm_num), fun δ hδ hδ0 => ?_⟩
  have hδ9' : δ < δ9 := lt_of_lt_of_le hδ0 (min_le_left _ _)
  have hδ30 : δ ≤ 1 / 30 := hδ0.le.trans (min_le_right _ _)
  obtain ⟨κ9, hκ9, N9, hN9⟩ := h9' δ hδ hδ9'
  refine ⟨κ9 / 4, by positivity, fun κ hκ hκle => ?_⟩
  obtain ⟨N3, hN3⟩ := EvenMinorSupplyJ200.log_F_sq_le_calE_quarter γ 1 h1 h2 one_pos
  obtain ⟨N2, hN2⟩ := KernelMomentSupplyJ200.four_le_calE γ κ h2 hκ
  obtain ⟨N5, hN5⟩ := calE_le_F_pow γ (2 * κ) δ h1 h2 hδ
  obtain ⟨N6, hN6⟩ := calE_le_F_pow γ (5 / 4 + 2 * κ9) (5 * δ) h1 h2 (by positivity)
  refine ⟨42 * Real.log 4 * 14404 ^ 2, by positivity,
    max (max (max N3 N2) (max N5 N6)) (max N9 16), fun N hN => ?_⟩
  have hN3' : N3 ≤ N := le_trans (by simp) hN
  have hN2' : N2 ≤ N := le_trans (by simp) hN
  have hN5' : N5 ≤ N := le_trans (by simp) hN
  have hN6' : N6 ≤ N := le_trans (by simp) hN
  have hN9' : N9 ≤ N := le_trans (by simp) hN
  have hN16 : 16 ≤ N := le_trans (by simp) hN
  have hN1 : 1 ≤ N := by omega
  have hX : 2 ≤ F γ N := two_le_F γ h1 N hN16
  have hlX1 : 1 ≤ Real.log (F γ N) := one_le_log_F γ h1 N hN16
  have hE4 : 4 ≤ calE γ κ N := hN2 N hN2'
  have hE0 : 0 < calE γ κ N := by linarith
  have hΔeq : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = calE γ κ N ^ (-(2 / 3 : ℝ)) :=
    EvenMinorSupplyJ200.calE_two_mul γ κ N
  have hΔ0 : 0 < calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) := by
    rw [hΔeq]; exact Real.rpow_pos_of_pos hE0 _
  have hΔ1 : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) < 1 := by
    rw [hΔeq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  set P := F γ N ^ (6 * δ) with hPdef
  set X := F γ N with hXdef
  set Δ := calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) with hΔdef
  set E := calE γ κ N with hEdef
  set A := (majorArcs P X)ᶜ ∩ Set.Icc (-E) E with hAdef
  set T₀ := (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) with hT₀def
  set c := calE γ κ9 N ^ (2 / 3 : ℝ) with hcdef
  set r := X ^ (δ - 1) with hrdef
  set lX := Real.log X with hlXdef
  set V := 14404 * X ^ (1 - 3 * δ) * lX ^ 4 with hVdef
  set u := E ^ (1 / 3 : ℝ) with hudef
  have hX0 : 0 < X := by linarith
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hX0 _).le
  have hu0 : 0 < u := Real.rpow_pos_of_pos hE0 _
  have hc1 : 1 ≤ c := Real.one_le_rpow
    (by unfold calE; exact Real.one_le_exp (mul_nonneg hκ9.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast hN1)) _))) (by norm_num)
  have hV0 : 0 ≤ V := by positivity
  have hAm : MeasurableSet A :=
    (PrimeKernel264.measurableSet_majorArcs P X).compl.inter measurableSet_Icc
  haveI : IsFiniteMeasure (volume.restrict A) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono Set.inter_subset_right).trans_lt measure_Icc_lt_top⟩
  let g : ℝ → ℝ := fun α => ‖Sp P X α ^ 2 * evenKernel Δ α‖
  let φ : ℝ × ℝ → ℝ := fun z => ‖Phio γ N (z.2 - z.1)‖
  let G : ℝ × ℝ → ℝ := fun z => g z.1 * g z.2 * φ z
  have hPc : Continuous (Phio γ N) := by unfold Phio eC; fun_prop
  have hφc : Continuous φ := (hPc.comp (continuous_snd.sub continuous_fst)).norm
  have hgc : Continuous g :=
    (((by unfold Sp eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).norm
  have hgI : Integrable g := by
    simpa only [g, KernelMomentSupplyJ200.integrand, norm_mul, U1539.norm_eC, mul_one] using
      (KernelMomentSupplyJ200.total_integrable P X Δ 0 hΔ0 hΔ1).norm
  have hgi : Integrable g (volume.restrict A) := hgI.integrableOn
  have hcard : ∀ x, ‖Phio γ N x‖ ≤ N := by
    intro x
    unfold Phio
    refine (norm_sum_le _ _).trans ?_
    simp only [U1539.norm_eC, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h := (Finset.card_filter_le (Finset.Ioc (N / 2) N) (fun n => ¬ Even (nu γ n))).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
    exact_mod_cast h
  have hgg : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2)
      ((volume.restrict A).prod (volume.restrict A)) := hgi.mul_prod hgi
  have hint : Integrable G ((volume.restrict A).prod (volume.restrict A)) := by
    refine (hgg.const_mul (N : ℝ)).mono'
      (((hgc.comp continuous_fst).mul (hgc.comp continuous_snd)).mul hφc).aestronglyMeasurable
      (Eventually.of_forall (fun z => ?_))
    have hp : 0 ≤ g z.1 * g z.2 := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (norm_nonneg _))]
    have := mul_le_mul_of_nonneg_left (hcard (z.2 - z.1)) hp
    change g z.1 * g z.2 * ‖Phio γ N (z.2 - z.1)‖ ≤ (N : ℝ) * (g z.1 * g z.2)
    linarith
  set S : Set (ℝ × ℝ) := {z : ℝ × ℝ | T₀ < φ z} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hφc.measurable
  -- the minor arc bound for `g`
  have hgβ : ∀ β ∈ A, g β ≤ V ^ 2 := by
    intro β hβ
    have hs := VaughanSupplyJ200.minor_vaughan_real P X β hX
      (Real.one_le_rpow (by linarith) (by positivity))
      (by
        have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X)
          (show 6 * δ ≤ 1 by linarith)
        simpa only [Real.rpow_one] using hh) hβ.1
    have hsv := hs.trans (vaughan_scalar X δ (by linarith) hlX1 hδ.le hδ30)
    have hk : ‖evenKernel Δ β‖ ≤ 1 := by
      rw [KernelMomentSupplyJ200.norm_evenKernel]
      have h := KernelTail385.kernel_abs_le_two_sub Δ ((1 / 2) * β) hΔ0 hΔ1
      linarith
    change ‖Sp P X β ^ 2 * evenKernel Δ β‖ ≤ V ^ 2
    rw [norm_mul, norm_pow]
    calc ‖Sp P X β‖ ^ 2 * ‖evenKernel Δ β‖ ≤ ‖Sp P X β‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hk (sq_nonneg _)
      _ ≤ V ^ 2 := by rw [mul_one]; exact pow_le_pow_left₀ (norm_nonneg _) hsv 2
  -- the Lemma 9 threshold and range
  have hthr : (N : ℝ) * calE γ κ9 N ^ (-(1 / 3 : ℝ)) ≤ T₀ := by
    rw [hT₀def, calE_rpow, calE_rpow]
    exact mul_le_mul_of_nonneg_left (calE_mono γ _ _ N hN1 (by linarith)) (Nat.cast_nonneg N)
  have hrange : 2 * E ≤ X ^ δ := by
    have h2E : 2 * E ≤ calE γ (2 * κ) N := by
      rw [show 2 * κ = κ + κ by ring, ← calE_mul]
      nlinarith
    exact h2E.trans (hN5 N hN5')
  -- the index set of `h`
  set H : ℤ := ⌊c⌋ with hHdef
  set hs : Finset ℤ := Finset.Icc (-H) H with hsdef
  have hH0 : 0 ≤ H := Int.floor_nonneg.mpr (by linarith)
  have hcardh : (hs.card : ℝ) ≤ 3 * c := by
    have hc' : hs.card = (2 * H + 1).toNat := by
      rw [hsdef, Int.card_Icc]; congr 1; ring
    rw [hc', show ((2 * H + 1).toNat : ℝ) = ((2 * H + 1 : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg (by omega)]
    push_cast
    have := Int.floor_le c
    linarith
  -- the fiber bound
  have hfib : ∀ α ∈ A, (∫ β, S.indicator G (α, β) ∂(volume.restrict A)) ≤
      g α * ((N : ℝ) * V ^ 2 * (hs.card * (2 * r))) := by
    intro α hα
    let U : Set ℝ := ⋃ h ∈ hs, Set.Icc (α + (h : ℝ) / 2 - r) (α + (h : ℝ) / 2 + r)
    have hU : MeasurableSet U :=
      Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Icc)
    have hga : 0 ≤ g α := norm_nonneg _
    have hcst : 0 ≤ g α * ((N : ℝ) * V ^ 2) := by positivity
    have hfb := fiber_bound A hAm (fun β => S.indicator G (α, β))
      (fun β => Set.indicator_nonneg (fun z _ => mul_nonneg (mul_nonneg (norm_nonneg _)
        (norm_nonneg _)) (norm_nonneg _)) _) U hU (g α * ((N : ℝ) * V ^ 2)) hcst
      (fun β hβ => ?_) (hs.card * (2 * r)) (by positivity)
      (union_volume hs (fun h => α + (h : ℝ) / 2) r hr0)
    · calc _ ≤ _ := hfb
        _ = _ := by ring
    · by_cases hb : (α, β) ∈ S
      · rw [Set.indicator_of_mem hb]
        have hb' : T₀ < ‖Phio γ N (β - α)‖ := hb
        have hab : |β - α| ≤ X ^ δ := by
          have h1' := abs_le.mpr ⟨hα.2.1, hα.2.2⟩
          have h2' := abs_le.mpr ⟨hβ.2.1, hβ.2.2⟩
          have := abs_sub (β) (α)
          linarith
        obtain ⟨h, hh, hhr⟩ := hN9 N hN9' (β - α) hab (lt_of_le_of_lt hthr hb')
        have hmem : β ∈ U := by
          refine Set.mem_iUnion₂.mpr ⟨h, ?_, ?_⟩
          · rw [hsdef, Finset.mem_Icc]
            have hhc : (h : ℝ) ≤ c ∧ -(h : ℝ) ≤ c := by
              constructor
              · exact (le_abs_self _).trans (by exact_mod_cast hh)
              · exact (neg_le_abs _).trans (by exact_mod_cast hh)
            constructor
            · have := Int.le_floor.mpr (show ((-h : ℤ) : ℝ) ≤ c by push_cast; exact hhc.2)
              omega
            · exact Int.le_floor.mpr hhc.1
          · rw [Set.mem_Icc]
            have := abs_le.mp hhr
            constructor <;> linarith [this.1, this.2]
        rw [Set.indicator_of_mem hmem]
        change g α * g β * ‖Phio γ N (β - α)‖ ≤ g α * ((N : ℝ) * V ^ 2)
        have hgb := hgβ β hβ
        have hgb0 : 0 ≤ g β := norm_nonneg _
        have hP := hcard (β - α)
        calc g α * g β * ‖Phio γ N (β - α)‖ ≤ g α * V ^ 2 * N := by gcongr
          _ = _ := by ring
      · rw [Set.indicator_of_notMem hb]
        exact Set.indicator_nonneg (fun _ _ => hcst) _
  have hmain := large_fubini A hAm g G S hSm hint hgi _ hfib
  -- the `L¹` bound
  have hL1 : (∫ x, g x ∂(volume.restrict A)) ≤ 7 * Real.log 4 * X * lX * u := by
    have h23 : Real.sqrt Δ = u⁻¹ := by
      rw [hΔeq, show (-(2 / 3 : ℝ)) = (1 / 3) * (-2) by norm_num,
        Real.rpow_mul hE0.le, ← hudef, Real.rpow_neg hu0.le, Real.sqrt_inv]
      norm_num
      rw [Real.sqrt_sq hu0.le]
    have h := (setIntegral_le_integral (s := A) hgI (Eventually.of_forall
      (fun _ => norm_nonneg _))).trans
      (KernelMomentSupplyJ200.shifted_weighted_mass_sqrt P X Δ hX hΔ0 hΔ1)
    rw [h23, div_inv_eq_mul] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  -- the growth condition
  have hgrow : lX ^ 9 * c * u ^ 2 ≤ X ^ (5 * δ) := by
    have hl9 : lX ^ 9 ≤ calE γ (1 * (1 / 4) * 5) N := by
      have h10 : lX ^ 9 ≤ (lX ^ 2) ^ 5 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hlX1 (by norm_num)
      have hq := hN3 N hN3'
      rw [calE_rpow] at hq
      refine h10.trans ((pow_le_pow_left₀ (sq_nonneg _) hq 5).trans (le_of_eq ?_))
      rw [← Real.rpow_natCast, calE_rpow]
      norm_num
    have hcc : c ≤ calE γ κ9 N := by
      rw [hcdef, calE_rpow]; exact calE_mono γ _ _ N hN1 (by nlinarith)
    have huu : u ^ 2 ≤ calE γ κ9 N := by
      rw [hudef, hEdef, calE_rpow, sq, calE_mul]
      exact calE_mono γ _ _ N hN1 (by linarith)
    have hprod : lX ^ 9 * c * u ^ 2 ≤
        calE γ (1 * (1 / 4) * 5) N * calE γ κ9 N * calE γ κ9 N := by
      have hl0 : 0 ≤ lX ^ 9 := by positivity
      have hc0 : 0 ≤ c := by linarith
      have hE5 : 0 ≤ calE γ (1 * (1 / 4) * 5) N := (Real.exp_pos _).le
      have hE9 : 0 ≤ calE γ κ9 N := (Real.exp_pos _).le
      calc lX ^ 9 * c * u ^ 2 ≤ calE γ (1 * (1 / 4) * 5) N * calE γ κ9 N * u ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul hl9 hcc hc0 hE5) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left huu (mul_nonneg hE5 hE9)
    refine hprod.trans ?_
    rw [calE_mul, calE_mul]
    refine le_trans (le_of_eq ?_) (hN6 N hN6')
    congr 1
    ring
  have hfin := large_arith N X δ u c lX (∫ x, g x ∂(volume.restrict A)) V
    (hs.card * (2 * r)) (Nat.cast_nonneg N) (by linarith) hu0
    (by linarith) (by linarith) (integral_nonneg (fun _ => norm_nonneg _)) hL1 hV0 le_rfl
    (by positivity) (by
      have h2r : 0 ≤ 2 * r := by positivity
      calc (hs.card : ℝ) * (2 * r) ≤ 3 * c * (2 * r) := mul_le_mul_of_nonneg_right hcardh h2r
        _ = _ := by rw [hrdef]) hgrow
  have hu' : u⁻¹ = E ^ (-(1 / 3 : ℝ)) := by rw [hudef, Real.rpow_neg hE0.le]
  rw [hu'] at hfin
  exact hmain.trans hfin

/-- P0082 page 369 after (39), the absolute Gram integral for display (30):
`∫∫_{𝔫_Y × 𝔫_Y} |S(α)² K_e(α)| |S(β)² K_e(β)| |Φ_o(β - α)| dα dβ ≪ N X² ℰ^{-1/3}`, with the even
weights, equal to the odd ones. The proof of `KernelMomentSteps.even_gram_bound` with `Φ_o`:
the split at `N ℰ(2κ)^{-2/3}`, the `L¹` bound and the large part
`odd_gram_large_of_lemma9odd`. CONDITIONAL ON the odd Lemma 9 as the hypothesis `h9`. -/
theorem odd_gram_bound_of_lemma9odd (h9 : Lemma9odd) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∫ z : ℝ × ℝ,
            ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.1 ^ 2 *
                evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.1‖ *
              ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.2 ^ 2 *
                evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.2‖ *
              ‖Phio γ N (z.2 - z.1)‖
            ∂(volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N))).prod
              (volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N)))) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hL⟩ := odd_gram_large_of_lemma9odd h9 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  obtain ⟨κ₀, hκ₀, hL2⟩ := hL δ hδ hδ₀'
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₁, hN₁⟩ := hL2 κ hκ hκle
  obtain ⟨N₃, hN₃⟩ := EvenMinorSupplyJ200.log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  refine ⟨49 * Real.log 4 ^ 2 + B, by positivity, max (max N₁ N₃) 16, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  have hX : 2 ≤ F γ N := two_le_F γ h1 N hN16
  have hE1 : 1 ≤ calE γ κ N := by
    unfold calE
    exact Real.one_le_exp (mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _))
  have hE0 : 0 < calE γ κ N := by linarith
  have hΔeq : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = calE γ κ N ^ (-(2 / 3 : ℝ)) :=
    EvenMinorSupplyJ200.calE_two_mul γ κ N
  have hΔ0 : 0 < calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) := by
    rw [hΔeq]; exact Real.rpow_pos_of_pos hE0 _
  have hΔ1 : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) < 1 := by
    rw [hΔeq]
    have h4 : 1 < calE γ κ N := by
      unfold calE
      exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos
        (Real.log_pos (by exact_mod_cast (by omega : 1 < N))) _))
    exact Real.rpow_lt_one_of_one_lt_of_neg h4 (by norm_num)
  set P := F γ N ^ (6 * δ)
  set X := F γ N
  set Δ := calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))
  set E := calE γ κ N
  set A := (majorArcs P X)ᶜ ∩ Set.Icc (-E) E
  let g : ℝ → ℝ := fun α => ‖Sp P X α ^ 2 * evenKernel Δ α‖
  let φ : ℝ × ℝ → ℝ := fun z => ‖Phio γ N (z.2 - z.1)‖
  have hPc : Continuous (Phio γ N) := by unfold Phio eC; fun_prop
  have hφc : Continuous φ := (hPc.comp (continuous_snd.sub continuous_fst)).norm
  have hgc : Continuous g :=
    (((by unfold Sp eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).norm
  have hgI : Integrable g := by
    simpa only [g, integrand, norm_mul, U1539.norm_eC, mul_one] using
      (total_integrable P X Δ 0 hΔ0 hΔ1).norm
  have hgi : Integrable g (volume.restrict A) := hgI.integrableOn
  have hcard : ∀ x, ‖Phio γ N x‖ ≤ N := by
    intro x
    unfold Phio
    refine (norm_sum_le _ _).trans ?_
    simp only [U1539.norm_eC, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h := (Finset.card_filter_le (Finset.Ioc (N / 2) N) (fun n => ¬ Even (nu γ n))).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
    exact_mod_cast h
  have hgg : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2)
      ((volume.restrict A).prod (volume.restrict A)) := hgi.mul_prod hgi
  have hint : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2 * φ z)
      ((volume.restrict A).prod (volume.restrict A)) := by
    refine (hgg.const_mul (N : ℝ)).mono'
      (((hgc.comp continuous_fst).mul (hgc.comp continuous_snd)).mul hφc).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    have hp : 0 ≤ g z.1 * g z.2 := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (norm_nonneg _))]
    have := mul_le_mul_of_nonneg_left (hcard (z.2 - z.1)) hp
    change g z.1 * g z.2 * ‖Phio γ N (z.2 - z.1)‖ ≤ (N : ℝ) * (g z.1 * g z.2)
    linarith
  have hT₀ : 0 ≤ (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (Real.exp_pos _).le _)
  have hsplit := gram_split (volume.restrict A) g φ (fun _ => norm_nonneg _)
    hφc.measurable hgi hint _ hT₀
  have hL1 : (∫ x, g x ∂(volume.restrict A)) ≤
      7 * (Real.log 4 * X * Real.log X) / Real.sqrt (E ^ (-(2 / 3 : ℝ))) := by
    rw [← hΔeq]
    exact (setIntegral_le_integral hgI (Filter.Eventually.of_forall
      (fun _ => norm_nonneg _))).trans (shifted_weighted_mass_sqrt P X Δ hX hΔ0 hΔ1)
  have hsmall := small_part_le N X E _ (Nat.cast_nonneg N) hX hE1 (hN₃ N hN3)
    (integral_nonneg (fun _ => norm_nonneg _)) hL1
  rw [← calE_two_mul_twothirds] at hsmall
  have hlarge := hN₁ N hN1
  calc _ ≤ _ := hsplit
    _ ≤ 49 * Real.log 4 ^ 2 * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      refine add_le_add ?_ hlarge
      calc _ = (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) *
            (∫ x, g x ∂(volume.restrict A)) ^ 2 := by ring
        _ ≤ _ := hsmall
    _ = _ := by ring

/-- P0082 page 369 after (39), display (30) from the right side of the cognate of (32): the
exact statement of `Display29Steps.leaf_odd_kernel_moment`, CONDITIONAL ON the odd Lemma 9 as
the hypothesis `h9`. The tail removal at `Y = ℰ` and the squaring are `moment_tail_gram_odd`, the
absolute double integral is `odd_gram_bound_of_lemma9odd`, the tail term is
`KernelMomentSupplyJ200.tail_sq_le`. The proof of `KernelMomentSteps.even_kernel_moment_of_steps`
with `K_o`, `𝒩_o` and `Φ_o`. -/
theorem odd_kernel_moment_of_lemma9odd (h9 : Lemma9odd) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => ¬ Even (nu γ n)),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ,
              Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
                oddKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) α *
                  eC (-(α * F γ n))‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hL⟩ := odd_gram_bound_of_lemma9odd h9 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  obtain ⟨κ₀, hκ₀, hL2⟩ := hL δ hδ hδ₀'
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₁, hN₁⟩ := hL2 κ hκ hκle
  obtain ⟨N₂, hN₂⟩ := four_le_calE γ κ h2 hκ
  obtain ⟨N₃, hN₃⟩ := EvenMinorSupplyJ200.log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  refine ⟨2 * B + 128 * Real.log 4 ^ 2, by positivity, max (max N₁ N₂) (max N₃ 16),
    fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  set E := calE γ κ N with hEdef
  set X := F γ N with hXdef
  set P := F γ N ^ (6 * δ) with hPdef
  have hE4 : 4 ≤ E := hN₂ N hN2
  have hX : 2 ≤ X := two_le_F γ h1 N hN16
  have hΔeq : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = E ^ (-(2 / 3 : ℝ)) :=
    EvenMinorSupplyJ200.calE_two_mul γ κ N
  set Δ := calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) with hΔdef
  have hE0 : 0 < E := by linarith
  have hΔ0 : 0 < Δ := by rw [hΔeq]; exact Real.rpow_pos_of_pos hE0 _
  have hΔ1 : Δ < 1 := by
    rw [hΔeq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  let s := (Finset.Ioc (N / 2) N).filter (fun n => ¬ Even (nu γ n))
  have hmt := moment_tail_gram_odd P X Δ E hX hΔ0 hΔ1 hE4 (majorArcs P X)ᶜ s (fun n => F γ n)
  have hgram := hN₁ N hN1
  have htail : (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * E)) ^ 2 ≤
      64 * Real.log 4 ^ 2 * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
    rw [hΔeq]
    exact tail_sq_le X E hX (by linarith) (hN₃ N hN3)
  have hcard : (s.card : ℝ) ≤ N := by
    have h := (Finset.card_filter_le (Finset.Ioc (N / 2) N) (fun n => ¬ Even (nu γ n))).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
    exact_mod_cast h
  have hEn : 0 ≤ E ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos hE0 _).le
  have hXn : 0 ≤ X ^ 2 := sq_nonneg _
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl4 : 0 ≤ Real.log 4 ^ 2 := sq_nonneg _
  have hτ0 : 0 ≤ (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * E)) ^ 2 := sq_nonneg _
  have hsum : (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ, Sp P X α ^ 2 * oddKernel Δ α *
      eC (-(α * F γ n))‖ ^ 2) ≤
      2 * (B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) +
        2 * N * (64 * Real.log 4 ^ 2 * X ^ 2 * E ^ (-(1 / 3 : ℝ))) := by
    refine hmt.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hgram (by norm_num)
    · have h3 := mul_le_mul hcard htail hτ0 hNn
      nlinarith [h3]
  calc _ ≤ 2 * (B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) +
        2 * N * (64 * Real.log 4 ^ 2 * X ^ 2 * E ^ (-(1 / 3 : ℝ))) := hsum
    _ = (2 * B + 128 * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by ring

end LeanLab.ExceptionalSet.OddKernelMomentSupplyJ200
