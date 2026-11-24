import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Remainder66Split
import LeanLab.ExceptionalSet.Wire1122Lemma55

/-!
# Split of the LEAF `mv_64_tilde_remainder` of `Lemma3MV617Integral`

Burst burst-20261122, Claude cloud session S112, step mv64_tilde_split.

Source P0015, Montgomery and Vaughan 1975, journal pages 361 to 364, displays (6.1) to (6.9)
with the exceptional additions (6.2̃), (6.4̃), (6.6̃), (6.7̃). The split mirrors the proved
non exceptional split `Lemma2MV/Remainder66Split.lean` of `mv_remainder_66_68`.

* REUSED, PROVED: `Lemma2MVSplit.rem66_arc_decomp`, `R₁(n)` as the sum over `q ≤ P` of the arc
  sums of (6.4), and `Lemma2MVSplit.rem66_two_P_le`.
* DEFINITIONS, each a display of P0015: `WnormExc`, the `W(ψ)` of (6.5) with the exceptional
  `W(χ̃)` of page 361 in place for `ψ = χ̃`; `A2exc`, `A3exc`, `A4exc`, the `q` terms of the sums
  of (6.6) and (6.6̃).
* LEAF `mv64t_arc_cs`, HARD: (6.1), (6.2̃), (6.3), (6.4̃) together with Cauchy Schwarz and
  (6.6), (6.6̃), (6.7), (6.7̃), for one modulus `q`.
* PROVED `mv64t_group_second` and `mv64t_group_third`: (6.8) with the exceptional `W`, by the
  proved Lemma 5.5 `Wire1122Lemma55.rem66_lemma55_proved`, following the proofs of
  `rem66_group_second_of` and `rem66_group_third_of`, with `Wsum_eq_mvWtilde`, PROVED.
* PROVED `mv64t_group_exc`: (6.8) for the new sum of (6.6̃), by Lemma 5.5 with `χ₁ = χ̃`.
* PROVED from these: `mv_64_tilde_remainder_of_leaves`, type checked equal to
  `type_of% @Lemma3MV617Integral.mv_64_tilde_remainder`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1 eC)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
  (T mainWeight arcIntegral Wnorm mvW rem66_cchi rem66_arcSum rem66_arc_decomp rem66_two_P_le rem66_lemma55
    rem66_group_by_primitive rem66_group_sum rem66_tau_principal)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (Ttilde mvWtilde WnormTilde)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
  (tauInd excWeight crossWeight arcTt arcTTt)

/-! ### Definitions, each a display of P0015 -/

open Classical in
/-- P0015 page 361 and (6.6̃): the norm `W(ψ)` of a character `ψ` of modulus `s`, which for
`ψ = χ̃` is the exceptional `W(χ̃)`, built from `W(χ̃,η) = S(χ̃,η) - T̃(η)`, the lab's
`WnormTilde`, and otherwise the `W(ψ)` of (6.5). -/
noncomputable def WnormExc {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) {s : ℕ}
    (ψ : DirichletCharacter ℂ s) : ℝ :=
  if h : s = r then
    (if (h ▸ ψ : DirichletCharacter ℂ r) = χ then WnormTilde β P X ψ else Wnorm P X ψ)
  else Wnorm P X ψ

/-- The `q` term of the first sum of P0015 display (6.6), page 362, in the exceptional case of
(6.6̃): `μ(q)² φ(q)⁻² Σ_ψ |c_ψ(-n) τ(ψ̄)| W(ψ*)` with the exceptional `W(χ̃)`. -/
noncomputable def A2exc {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
    ∑ᶠ ψ : DirichletCharacter ℂ q,
      ‖rem66_cchi ψ (-(n : ℤ)) * rem66_cchi ψ⁻¹ 1‖ * WnormExc β P X χ ψ.primitiveCharacter

/-- The `q` term of the second sum of P0015 display (6.6), page 362, in the exceptional case of
(6.6̃): `φ(q)⁻² Σ_{ψ,ψ'} |c_{ψψ'}(-n) τ(ψ̄) τ(ψ̄')| W(ψ*) W(ψ'*)` with the exceptional `W(χ̃)`. -/
noncomputable def A3exc {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℝ :=
  1 / (q.totient : ℝ) ^ 2 *
    ∑ᶠ ψ : DirichletCharacter ℂ q, ∑ᶠ ψ' : DirichletCharacter ℂ q,
      ‖rem66_cchi (ψ * ψ') (-(n : ℤ)) * rem66_cchi ψ⁻¹ 1 * rem66_cchi ψ'⁻¹ 1‖ *
        WnormExc β P X χ ψ.primitiveCharacter * WnormExc β P X χ ψ'.primitiveCharacter

/-- The `q` term of the new sum of P0015 display (6.6̃), page 362, from the terms
`T̃(η) W(ψ,η)` of (6.4̃), without the factor `2X^{1/2}` from (6.7̃):
`|τ(χ̄̃χ₀)| φ(q)⁻² Σ_ψ |c_{χ̃χ₀ψ}(-n) τ(ψ̄)| W(ψ*)`, present only when `r̃ ∣ q`; for the real
`χ̃` of the parent leaf `τ(χ̄̃χ₀) = τ(χ̃χ₀)`. -/
noncomputable def A4exc {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℝ :=
  if h : r ∣ q then
    ‖rem66_cchi (DirichletCharacter.changeLevel h χ)⁻¹ 1‖ / (q.totient : ℝ) ^ 2 *
      ∑ᶠ ψ : DirichletCharacter ℂ q,
        ‖rem66_cchi (DirichletCharacter.changeLevel h χ * ψ) (-(n : ℤ)) * rem66_cchi ψ⁻¹ 1‖ *
          WnormExc β P X χ ψ.primitiveCharacter
  else 0

lemma WnormExc_nonneg {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) {s : ℕ}
    (ψ : DirichletCharacter ℂ s) : 0 ≤ WnormExc β P X χ ψ := by
  unfold WnormExc WnormTilde Wnorm
  split_ifs <;> exact Real.sqrt_nonneg _

lemma A2exc_nonneg {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (q n : ℕ) :
    0 ≤ A2exc β P X χ q n := by
  unfold A2exc
  refine mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (finsum_nonneg (fun ψ => ?_))
  exact mul_nonneg (norm_nonneg _) (WnormExc_nonneg _ _ _ _ _)

/-! ### Display (6.8) with the exceptional `W`, proved -/

open DirichletCharacter in
/-- P0015 display (6.8), page 362, the first sum with the exceptional `W` of (6.6̃), PROVED from
Lemma 5.5 exactly as `Lemma2MVSplit.rem66_group_second_of`, the bound written with
`Σ_{r≤P} Σ*_ψ W(ψ)` for the exceptional norms. -/
theorem mv64t_group_second_aux (hL : type_of% @rem66_lemma55) : ∃ C : ℝ, 0 < C ∧
    ∀ (P X β : ℝ) {k : ℕ} (χt : DirichletCharacter ℂ k) (n : ℕ), 1 ≤ n →
    ∑ q ∈ Icc 1 ⌊P⌋₊, A2exc β P X χt q n ≤ C * ((n : ℝ) / (n.totient : ℝ)) *
      (∑ r ∈ Icc 1 ⌊P⌋₊, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
        WnormExc β P X χt ψ.1) := by
  classical
  obtain ⟨C, hC, h55⟩ := hL
  refine ⟨C, hC, fun P X β k χt n hn => ?_⟩
  set N := ⌊P⌋₊
  set ρ := (n : ℝ) / (n.totient : ℝ)
  set F : (q : ℕ) → DirichletCharacter ℂ q → ℝ := fun q χ =>
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      ‖rem66_cchi χ (-(n : ℤ)) * rem66_cchi χ⁻¹ 1‖ with hF
  set D : ℕ → ℕ → ℝ := fun q r => if h : r ∣ q then
      ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
        F q (changeLevel h ψ.1) * WnormExc β P X χt ψ.1 else 0 with hD
  have step1 : ∀ q ∈ Icc 1 N, A2exc β P X χt q n = ∑ r ∈ Icc 1 N, D q r := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqN : q ≤ N := (mem_Icc.mp hq).2
    have e1 : A2exc β P X χt q n = ∑ᶠ χ : DirichletCharacter ℂ q,
        F q χ * (fun r (ψ : DirichletCharacter ℂ r) => WnormExc β P X χt ψ) χ.conductor
          χ.primitiveCharacter := by
      unfold A2exc
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, mul_sum]
      refine sum_congr rfl (fun χ _ => ?_)
      simp only [hF]; ring
    rw [e1, rem66_group_by_primitive hq1 (F q) (fun r ψ => WnormExc β P X χt ψ)]
    refine sum_subset (Icc_subset_Icc le_rfl hqN) (fun r hrN hrq => ?_)
    have : ¬ r ∣ q := by
      intro h; apply hrq; rw [mem_Icc] at hrN ⊢
      exact ⟨hrN.1, Nat.le_of_dvd (by omega) h⟩
    simp only [dif_neg this]
  rw [sum_congr rfl step1, sum_comm]
  rw [mul_sum]
  refine sum_le_sum (fun r hr => ?_)
  have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
  have hW : ∀ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, 0 ≤ WnormExc β P X χt ψ.1 :=
    fun ψ => WnormExc_nonneg _ _ _ _ _
  have e2 : ∑ q ∈ Icc 1 N, D q r = ∑ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
      (∑ q ∈ Icc 1 N, if h : r ∣ q then F q (changeLevel h ψ.1) else 0) * WnormExc β P X χt ψ.1 := by
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


open DirichletCharacter in
/-- P0015 display (6.8), page 362, the second sum with the exceptional `W` of (6.6̃), PROVED from
Lemma 5.5 exactly as `Lemma2MVSplit.rem66_group_third_of`. -/
theorem mv64t_group_third_aux (hL : type_of% @rem66_lemma55) : ∃ C : ℝ, 0 < C ∧
    ∀ (P X β : ℝ) {k : ℕ} (χt : DirichletCharacter ℂ k) (n : ℕ), 1 ≤ n →
    ∑ q ∈ Icc 1 ⌊P⌋₊, A3exc β P X χt q n ≤ C * ((n : ℝ) / (n.totient : ℝ)) *
      (∑ r ∈ Icc 1 ⌊P⌋₊, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
        WnormExc β P X χt ψ.1) ^ 2 := by
  classical
  obtain ⟨C, hC, h55⟩ := hL
  refine ⟨C, hC, fun P X β k χt n hn => ?_⟩
  set N := ⌊P⌋₊
  set ρ := (n : ℝ) / (n.totient : ℝ)
  set G : (q : ℕ) → DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℝ := fun q χ χ' =>
    ‖rem66_cchi (χ * χ') (-(n : ℤ)) * rem66_cchi χ⁻¹ 1 * rem66_cchi χ'⁻¹ 1‖ /
      (q.totient : ℝ) ^ 2 with hG
  set Wf : (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun r ψ => WnormExc β P X χt ψ with hWf
  set E : ℕ → ℕ → ℕ → ℝ := fun q r₁ r₂ => if h : r₁ ∣ q ∧ r₂ ∣ q then
      ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
        ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
          G q (changeLevel h.1 ψ₁.1) (changeLevel h.2 ψ₂.1) * WnormExc β P X χt ψ₁.1 * WnormExc β P X χt ψ₂.1
      else 0 with hE
  have step1 : ∀ q ∈ Icc 1 N, A3exc β P X χt q n = ∑ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, E q r₁ r₂ := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqN : q ≤ N := (mem_Icc.mp hq).2
    have e1 : A3exc β P X χt q n = ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
        (G q χ χ' * Wf χ.conductor χ.primitiveCharacter) *
          Wf χ'.conductor χ'.primitiveCharacter := by
      unfold A3exc
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
  set w : ℕ → ℝ := fun r => ∑ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, WnormExc β P X χt ψ.1
    with hw
  have hmv : (∑ r ∈ Icc 1 N, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, WnormExc β P X χt ψ.1) = ∑ r ∈ Icc 1 N, w r := by
    refine sum_congr rfl (fun r _ => ?_); rw [finsum_eq_sum_of_fintype]
  have hbound : ∀ r₁ ∈ Icc 1 N, ∀ r₂ ∈ Icc 1 N, ∑ q ∈ Icc 1 N, E q r₁ r₂ ≤ C * ρ * (w r₁ * w r₂) := by
    intro r₁ _ r₂ _
    set K : ℕ → {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive} →
        {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive} → ℝ := fun q ψ₁ ψ₂ =>
      if h : r₁ ∣ q ∧ r₂ ∣ q then G q (changeLevel h.1 ψ₁.1) (changeLevel h.2 ψ₂.1) else 0
      with hK
    have eq1 : ∑ q ∈ Icc 1 N, E q r₁ r₂ =
        ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
          ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
            (∑ q ∈ Icc 1 N, K q ψ₁ ψ₂) * (WnormExc β P X χt ψ₁.1 * WnormExc β P X χt ψ₂.1) := by
      calc ∑ q ∈ Icc 1 N, E q r₁ r₂
          = ∑ q ∈ Icc 1 N, ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
              ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
                K q ψ₁ ψ₂ * (WnormExc β P X χt ψ₁.1 * WnormExc β P X χt ψ₂.1) := by
            refine sum_congr rfl (fun q _ => ?_)
            by_cases h : r₁ ∣ q ∧ r₂ ∣ q
            · simp only [hE, hK, dif_pos h]
              refine sum_congr rfl (fun ψ₁ _ => sum_congr rfl (fun ψ₂ _ => by ring))
            · simp only [hE, hK, dif_neg h, zero_mul, sum_const_zero]
        _ = ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive}, ∑ q ∈ Icc 1 N,
              ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
                K q ψ₁ ψ₂ * (WnormExc β P X χt ψ₁.1 * WnormExc β P X χt ψ₂.1) := sum_comm
        _ = ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
              ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive}, ∑ q ∈ Icc 1 N,
                K q ψ₁ ψ₂ * (WnormExc β P X χt ψ₁.1 * WnormExc β P X χt ψ₂.1) :=
            sum_congr rfl (fun ψ₁ _ => sum_comm)
        _ = _ := by simp only [sum_mul]
    rw [eq1]
    have hw1 : w r₁ * w r₂ = ∑ ψ₁ : {ψ : DirichletCharacter ℂ r₁ // ψ.IsPrimitive},
        ∑ ψ₂ : {ψ : DirichletCharacter ℂ r₂ // ψ.IsPrimitive},
          WnormExc β P X χt ψ₁.1 * WnormExc β P X χt ψ₂.1 := by
      simp only [hw]; rw [sum_mul_sum]
    rw [hw1, mul_sum]
    refine sum_le_sum (fun ψ₁ _ => ?_)
    rw [mul_sum]
    refine sum_le_sum (fun ψ₂ _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (WnormExc_nonneg _ _ _ _ _) (WnormExc_nonneg _ _ _ _ _))
    have h1 := h55 r₁ r₂ ψ₁.1 ψ₂.1 ψ₁.2 ψ₂.2 (-(n : ℤ)) (by omega) N
    have hnat : (-(n : ℤ)).natAbs = n := by simp
    rw [hnat] at h1
    exact h1
  have hw0 : ∀ r, 0 ≤ w r := fun r => sum_nonneg (fun ψ _ => WnormExc_nonneg _ _ _ _ _)
  calc ∑ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, ∑ q ∈ Icc 1 N, E q r₁ r₂
      ≤ ∑ r₁ ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, C * ρ * (w r₁ * w r₂) :=
        sum_le_sum (fun r₁ h1 => sum_le_sum (fun r₂ h2 => hbound r₁ h1 r₂ h2))
    _ = C * ρ * (∑ r ∈ Icc 1 N, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, WnormExc β P X χt ψ.1) ^ 2 := by
        rw [hmv, sq, sum_mul_sum, mul_sum]
        refine sum_congr rfl (fun r₁ _ => ?_)
        rw [mul_sum]



open Classical in
/-- P0015 page 366, first display of section 7, exceptional case: the sum over moduli `r ≤ P` and
primitive `ψ` of `WnormExc` is the lab's `mvWtilde`, PROVED. -/
lemma Wsum_eq_mvWtilde {k : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ k) (hprim : χ.IsPrimitive)
    (hk1 : 1 ≤ k) (hkP : k ≤ ⌊P⌋₊) :
    ∑ r ∈ Icc 1 ⌊P⌋₊, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
      WnormExc β P X χ ψ.1 = mvWtilde β P X χ := by
  have key : ∀ r ∈ Icc 1 ⌊P⌋₊, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
      WnormExc β P X χ ψ.1 = ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
        Wnorm P X ψ.1 + (if r = k then WnormTilde β P X χ - Wnorm P X χ else 0) := by
    intro r _
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    by_cases h : r = k
    · subst h
      rw [if_pos rfl]
      have e : ∀ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, WnormExc β P X χ ψ.1 =
          Wnorm P X ψ.1 + (if ψ = ⟨χ, hprim⟩ then WnormTilde β P X χ - Wnorm P X χ else 0) := by
        intro ψ
        unfold WnormExc
        rw [dif_pos rfl]
        by_cases hψ : ψ = ⟨χ, hprim⟩
        · subst hψ; simp
        · have hψ' : ψ.1 ≠ χ := fun h => hψ (Subtype.ext h)
          simp [hψ, hψ']
      rw [sum_congr rfl (fun ψ _ => e ψ), sum_add_distrib, Finset.sum_ite_eq']
      simp
    · rw [if_neg h, add_zero]
      refine sum_congr rfl (fun ψ _ => ?_)
      unfold WnormExc
      rw [dif_neg h]
  rw [sum_congr rfl key, sum_add_distrib, Finset.sum_ite_eq']
  have hk : k ∈ Icc 1 ⌊P⌋₊ := mem_Icc.mpr ⟨hk1, hkP⟩
  rw [if_pos hk]
  unfold mvWtilde mvW
  ring

open DirichletCharacter in
/-- P0015 display (6.8), page 362, for the new sum of (6.6̃), PROVED from Lemma 5.5 with
`χ₁ = χ̃`: group `ψ` by its primitive `χ₂` and sum over `q ≡ 0 mod [r̃, r₂]`. -/
theorem mv64t_group_exc_aux (hL : type_of% @rem66_lemma55) : ∃ C : ℝ, 0 < C ∧
    ∀ (P X β : ℝ) {k : ℕ} (χt : DirichletCharacter ℂ k), χt.IsPrimitive → ∀ n : ℕ, 1 ≤ n →
    ∑ q ∈ Icc 1 ⌊P⌋₊, A4exc β P X χt q n ≤ C * ((n : ℝ) / (n.totient : ℝ)) *
      (∑ r ∈ Icc 1 ⌊P⌋₊, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
        WnormExc β P X χt ψ.1) := by
  classical
  obtain ⟨C, hC, h55⟩ := hL
  refine ⟨C, hC, fun P X β k χt hp n hn => ?_⟩
  set N := ⌊P⌋₊
  set ρ := (n : ℝ) / (n.totient : ℝ)
  set Wf : (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun r ψ => WnormExc β P X χt ψ with hWf
  set K : ℕ → (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun q r ψ =>
    if h : k ∣ q ∧ r ∣ q then
      ‖rem66_cchi (changeLevel h.1 χt * changeLevel h.2 ψ) (-(n : ℤ)) *
        rem66_cchi (changeLevel h.1 χt)⁻¹ 1 * rem66_cchi (changeLevel h.2 ψ)⁻¹ 1‖ /
        (q.totient : ℝ) ^ 2
    else 0 with hK
  set D : ℕ → ℕ → ℝ := fun q r =>
    ∑ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive}, K q r ψ.1 * Wf r ψ.1 with hD
  have step1 : ∀ q ∈ Icc 1 N, A4exc β P X χt q n = ∑ r ∈ Icc 1 N, D q r := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqN : q ≤ N := (mem_Icc.mp hq).2
    by_cases hk : k ∣ q
    · set Fq : DirichletCharacter ℂ q → ℝ := fun ψ =>
        ‖rem66_cchi (changeLevel hk χt)⁻¹ 1‖ / (q.totient : ℝ) ^ 2 *
          ‖rem66_cchi (changeLevel hk χt * ψ) (-(n : ℤ)) * rem66_cchi ψ⁻¹ 1‖ with hFq
      have e1 : A4exc β P X χt q n = ∑ ψ : DirichletCharacter ℂ q,
          Fq ψ * Wf ψ.conductor ψ.primitiveCharacter := by
        unfold A4exc
        rw [dif_pos hk, finsum_eq_sum_of_fintype, mul_sum]
        refine sum_congr rfl (fun ψ _ => ?_)
        simp only [hFq, hWf]; ring
      rw [e1, rem66_group_sum hq1 N hqN Fq Wf]
      refine sum_congr rfl (fun r _ => ?_)
      by_cases hr : r ∣ q
      · rw [dif_pos hr]
        refine sum_congr rfl (fun ψ _ => ?_)
        simp only [hK, hFq, dif_pos (And.intro hk hr)]
        rw [norm_mul, norm_mul, norm_mul]; ring
      · rw [dif_neg hr]
        refine (sum_eq_zero (fun ψ _ => ?_)).symm
        simp only [hK]; rw [dif_neg (fun h => hr h.2), zero_mul]
    · have e0 : A4exc β P X χt q n = 0 := by unfold A4exc; rw [dif_neg hk]
      rw [e0]
      refine (sum_eq_zero (fun r _ => sum_eq_zero (fun ψ _ => ?_))).symm
      simp only [hK]; rw [dif_neg (fun h => hk h.1), zero_mul]
  rw [sum_congr rfl step1, sum_comm, mul_sum]
  refine sum_le_sum (fun r _ => ?_)
  have e2 : ∑ q ∈ Icc 1 N, D q r = ∑ ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive},
      (∑ q ∈ Icc 1 N, K q r ψ.1) * Wf r ψ.1 := by
    simp only [hD, sum_mul]
    rw [sum_comm]
  rw [e2, finsum_eq_sum_of_fintype, mul_sum]
  refine sum_le_sum (fun ψ _ => ?_)
  refine mul_le_mul_of_nonneg_right ?_ (WnormExc_nonneg _ _ _ _ _)
  have h1 := h55 k r χt ψ.1 hp ψ.2 (-(n : ℤ)) (by omega) N
  have hnat : (-(n : ℤ)).natAbs = n := by simp
  rw [hnat] at h1
  exact h1

/-! ### Leaves -/

/-- LEAF: P0015 displays (6.1), (6.2̃), (6.3), (6.4̃), (6.6), (6.6̃), (6.7) and (6.7̃), pages 361
and 362, class HARD. For `α = a/q + η ∈ 𝔐(q,a)` expand `S(α)` by characters, (6.1), with
`S(χ₀,η) = T(η) + W(χ₀,η)`, `S(χ̃χ₀,η) = T̃(η) + W(χ̃χ₀,η)` when `r̃ ∣ q`, and `S(ψ,η) = W(ψ,η)`
otherwise; square and integrate over the arcs of modulus `q`, (6.4) with (6.4̃). The three main
terms are those of the parent leaf; each other term has a factor `W(ψ,η)` and is bounded by
Cauchy Schwarz with `∫|T|² ≤ X`, (6.7), `∫|T̃|² ≤ X`, (6.7̃), and `W(ψ,η) = W(ψ*,η)` on the
shorter interval, giving the sums (6.6) and (6.6̃). -/
theorem mv64t_arc_cs : ∃ C : ℝ, 0 < C ∧
    ∀ P X β : ℝ, 0 ≤ P → 0 < X → 2 * P ≤ X → β ≤ 1 →
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖rem66_arcSum P X q n -
            (mainWeight q n * arcIntegral P X q n + excWeight χ q n * arcTt β P X q n +
              2 * crossWeight χ q n * arcTTt β P X q n)‖ ≤
          C * (Real.sqrt X * (A2exc β P X χ q n + A4exc β P X χ q n) + A3exc β P X χ q n) := by
  sorry

/-- PROVED, planned as a LEAF of class MEDIUM: P0015 display (6.8), page 362, first sum, with
the exceptional `W` of (6.6̃) and page 366. Group the characters by the primitive character inducing them and apply
Lemma 5.5 with `χ₂` the character mod `1`, as in the proved
`Lemma2MVSplit.rem66_group_second_of`, now with `W(χ̃)` the exceptional norm. -/
theorem mv64t_group_second : ∃ C : ℝ, 0 < C ∧ ∀ P X β : ℝ,
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ n : ℕ, 1 ≤ n →
        ∑ q ∈ Icc 1 ⌊P⌋₊, A2exc β P X χ q n ≤
          C * ((n : ℝ) / (n.totient : ℝ)) * mvWtilde β P X χ := by
  obtain ⟨C, hC, h⟩ :=
    mv64t_group_second_aux LeanLab.ExceptionalSet.Wire1122Lemma55.rem66_lemma55_proved
  refine ⟨C, hC, fun P X β r _ χ hprim _ _ hr1 hrP n hn => ?_⟩
  rw [← Wsum_eq_mvWtilde β P X χ hprim hr1 (Nat.le_floor hrP)]
  exact h P X β χ n hn

/-- PROVED, planned as a LEAF of class MEDIUM: P0015 display (6.8), page 362, second sum, with
the exceptional `W` of (6.6̃) and page 366. Group both characters by primitive characters and apply Lemma 5.5, as in the
proved `Lemma2MVSplit.rem66_group_third_of`, now with `W(χ̃)` the exceptional norm. -/
theorem mv64t_group_third : ∃ C : ℝ, 0 < C ∧ ∀ P X β : ℝ,
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ n : ℕ, 1 ≤ n →
        ∑ q ∈ Icc 1 ⌊P⌋₊, A3exc β P X χ q n ≤
          C * ((n : ℝ) / (n.totient : ℝ)) * mvWtilde β P X χ ^ 2 := by
  obtain ⟨C, hC, h⟩ :=
    mv64t_group_third_aux LeanLab.ExceptionalSet.Wire1122Lemma55.rem66_lemma55_proved
  refine ⟨C, hC, fun P X β r _ χ hprim _ _ hr1 hrP n hn => ?_⟩
  rw [← Wsum_eq_mvWtilde β P X χ hprim hr1 (Nat.le_floor hrP)]
  exact h P X β χ n hn

/-- PROVED, planned as a LEAF of class HARD: P0015 display (6.8) for the new sum of (6.6̃),
page 362. Group `ψ` by its
primitive `χ₂` mod `r₂` and apply Lemma 5.5 with `χ₁ = χ̃` mod `r̃`, the sum over
`q ≡ 0 mod [r̃, r₂]` of `|τ(χ̃χ₀) τ(χ₂χ₀) c_{χ̃χ₂χ₀}(n)| φ(q)⁻²` being `≪ n φ(n)⁻¹`. -/
theorem mv64t_group_exc : ∃ C : ℝ, 0 < C ∧ ∀ P X β : ℝ,
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ n : ℕ, 1 ≤ n →
        ∑ q ∈ Icc 1 ⌊P⌋₊, A4exc β P X χ q n ≤
          C * ((n : ℝ) / (n.totient : ℝ)) * mvWtilde β P X χ := by
  obtain ⟨C, hC, h⟩ :=
    mv64t_group_exc_aux LeanLab.ExceptionalSet.Wire1122Lemma55.rem66_lemma55_proved
  refine ⟨C, hC, fun P X β r _ χ hprim _ _ hr1 hrP n hn => ?_⟩
  rw [← Wsum_eq_mvWtilde β P X χ hprim hr1 (Nat.le_floor hrP)]
  exact h P X β χ hprim n hn

/-! ### Assembly -/

/-- P0015 displays (6.1) to (6.9) with (6.2̃), (6.4̃), (6.6̃), (6.7̃), pages 361 to 364: the
exact type of `Lemma3MV617Integral.mv_64_tilde_remainder`, PROVED from the four leaves above and
the proved `rem66_arc_decomp`. -/
theorem mv_64_tilde_remainder_of_leaves : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 < C ∧
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖R1 (X ^ θ) X (n : ℤ) - ∑ q ∈ Icc 1 ⌊X ^ θ⌋₊,
            (mainWeight q n * arcIntegral (X ^ θ) X q n +
              excWeight χ q n * arcTt β (X ^ θ) X q n +
              2 * crossWeight χ q n * arcTTt β (X ^ θ) X q n)‖ ≤
          C * ((n : ℝ) / (n.totient : ℝ)) *
            (mvWtilde β (X ^ θ) X χ * Real.sqrt X + mvWtilde β (X ^ θ) X χ ^ 2) := by
  intro a _ha
  obtain ⟨C1, hC1, h1⟩ := mv64t_arc_cs
  obtain ⟨C2, hC2, h2⟩ := mv64t_group_second
  obtain ⟨C3, hC3, h3⟩ := mv64t_group_third
  obtain ⟨C4, hC4, h4⟩ := mv64t_group_exc
  refine ⟨C1 * (C2 + C4 + C3), by positivity, ?_⟩
  intro θ hθ hθ1
  have hδ : 0 < θ / 6 := by linarith
  have hδ1 : θ / 6 < 1 / 100 := by linarith
  have h6 : 6 * (θ / 6) = θ := by ring
  obtain ⟨X₁, hX₁⟩ := rem66_arc_decomp (θ / 6) hδ hδ1
  refine ⟨(max X₁ 4) ^ θ, ?_⟩
  intro X hX0 hP0 r hr1 _hr r_le _hsel hNZ χ β hprim hsq hne _hβlo hβ1 _hL n hn hnX
  have hM : max X₁ 4 ≤ X :=
    (Real.rpow_le_rpow_iff (by positivity) hX0.le hθ).mp hP0
  have hXa : X₁ ≤ X := le_trans (le_max_left _ _) hM
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_right _ _) hM
  have hdec := hX₁ X hXa n
  have hPX := rem66_two_P_le (θ / 6) X hδ hδ1 hX4
  rw [h6] at hdec hPX
  set P := X ^ θ with hPdef
  have hP0' : 0 ≤ P := Real.rpow_nonneg hX0.le _
  set s := Icc 1 ⌊P⌋₊ with hs
  have hqs : ∀ q ∈ s, 1 ≤ q ∧ (q : ℝ) ≤ P := fun q hq =>
    ⟨(mem_Icc.mp hq).1, le_trans (by exact_mod_cast (mem_Icc.mp hq).2) (Nat.floor_le hP0')⟩
  have hβ : β ≤ 1 := hβ1.le
  set W := mvWtilde β P X χ
  set ρ := (n : ℝ) / (n.totient : ℝ)
  have hρ : 0 < ρ := by
    have : 0 < n.totient := Nat.totient_pos.mpr (by omega)
    positivity
  have hS2 := h2 P X β r hNZ χ hprim hsq hne hr1 r_le n hn
  have hS3 := h3 P X β r hNZ χ hprim hsq hne hr1 r_le n hn
  have hS4 := h4 P X β r hNZ χ hprim hsq hne hr1 r_le n hn
  have hA2 : 0 ≤ ∑ q ∈ s, A2exc β P X χ q n := sum_nonneg (fun q _ => A2exc_nonneg _ _ _ _ _ _)
  have hW0 : 0 ≤ W := by
    by_contra hcon
    rw [not_le] at hcon
    have : C2 * ρ * W < 0 := mul_neg_of_pos_of_neg (by positivity) hcon
    linarith
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  rw [hdec, ← sum_sub_distrib]
  calc ‖∑ q ∈ s, (rem66_arcSum P X q n - (mainWeight q n * arcIntegral P X q n +
          excWeight χ q n * arcTt β P X q n + 2 * crossWeight χ q n * arcTTt β P X q n))‖
      ≤ ∑ q ∈ s, ‖rem66_arcSum P X q n - (mainWeight q n * arcIntegral P X q n +
          excWeight χ q n * arcTt β P X q n + 2 * crossWeight χ q n * arcTTt β P X q n)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ s, C1 * (Real.sqrt X * (A2exc β P X χ q n + A4exc β P X χ q n) +
          A3exc β P X χ q n) :=
        sum_le_sum (fun q hq => h1 P X β hP0' hX0 hPX hβ r hNZ χ hprim hsq hne hr1 r_le q
          (hqs q hq).1 (hqs q hq).2 n hn hnX)
    _ = C1 * (Real.sqrt X * (∑ q ∈ s, A2exc β P X χ q n + ∑ q ∈ s, A4exc β P X χ q n) +
          ∑ q ∈ s, A3exc β P X χ q n) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_add_distrib]
    _ ≤ C1 * (Real.sqrt X * (C2 * ρ * W + C4 * ρ * W) + C3 * ρ * W ^ 2) := by
        gcongr
    _ ≤ C1 * (C2 + C4 + C3) * ρ * (W * Real.sqrt X + W ^ 2) := by
        have e1 : 0 ≤ C1 * C3 * ρ * (W * Real.sqrt X) := by positivity
        have e2 : 0 ≤ C1 * (C2 + C4) * ρ * W ^ 2 := by positivity
        nlinarith

/-- Check that `mv_64_tilde_remainder_of_leaves` has exactly the type of
`Lemma3MV617Integral.mv_64_tilde_remainder`. -/
theorem mv_64_tilde_remainder_twin :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral.mv_64_tilde_remainder :=
  mv_64_tilde_remainder_of_leaves

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit.mv_64_tilde_remainder_of_leaves
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit.mv_64_tilde_remainder_twin
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit.mv64t_group_second
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit.mv64t_group_third
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit.Wsum_eq_mvWtilde
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit.mv64t_group_exc
