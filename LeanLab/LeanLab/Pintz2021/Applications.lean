/-
P0054 J. Pintz, "An approximate formula for Goldbach's problem with applications",
Riv. Mat. Univ. Parma 12 (2021), 181-199. Unit U-6771, session 20261020T2317Z-cloud53.
Read 2026-10-21 from the author's copy, real.mtak.hu/124681/1/Cikk2020Rivista.pdf, which has a
text layer; displays checked against the rendered pages.

The deductions of Sections 3 and 5 from the approximate formula, as CONDITIONAL theorems.
* `block_count`: the counting step common to (3.1) to (3.3) and (5.11) to (5.18): an even `m`
  with `R(m) = R₁(m) + R₂(m) > 0` is a Goldbach number, so the exceptions lie in the major arc
  exceptions or where `|R₂(m)| ≥ T`; the latter are counted by Chebyshev's inequality.
* `card_dvd_mul_le`, `card_dvd_mul_sq_le`: the Case 1 counts of Section 3 and of (5.14) and
  (5.15): `#{m ≤ N : R ∣ C m} ≤ C N / R` and `#{m ≤ N : R ∣ C m²} ≤ C N / √R`, PROVED.
* `theorem3_of_section3Input`: Theorem 3, `E(X) ≪_ε X^{0.72+ε}`, CONDITIONAL ON
  `Section3Input`, the paper's inputs (3.1), (3.5), (3.6) with Theorem 2, and Case 1 of
  Section 3, for every `ε`.
* `theorem5_of_section5Input`: Theorem 5, `E₂(N) ≪_ε N^{4/5+ε}`, CONDITIONAL ON
  `Section5Input`, the inputs (5.11), (5.16) with Theorem 2, and Case 1 (5.14), for every `ε`.
* `C0_pos`: `C₀ > 0`, since `C₀` is literally the lab's `ChenExplicit.twinC`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean
kernel.
-/
import Mathlib
import LeanLab.ExceptionalSet.Pintz2021
import LeanLab.ExceptionalSet.Pintz2018Reduction
import LeanLab.Pintz2021.Statements
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.Pintz2021.Applications
open Real Finset Filter Topology LeanLab.ExceptionalSet

attribute [local instance] Classical.propDecidable

/-! ### `C₀ > 0` -/

/-- The constant `C₀` of (2.4) is the lab's twin prime constant, by definition. -/
theorem C0_eq_twinC : C0 = LeanLab.ChenExplicit.twinC := rfl

theorem C0_pos : 0 < C0 := by rw [C0_eq_twinC]; exact LeanLab.ChenExplicit.twinC_pos

/-- `𝔖(m) ≥ 2 C₀ > 0` for every `m`, the hypothesis of `two_C0_le_Sing` discharged. -/
theorem two_C0_le_Sing' (m : ℕ) : 2 * C0 ≤ Sing m := two_C0_le_Sing m C0_pos.le

theorem Sing_pos (m : ℕ) : 0 < Sing m := by linarith [two_C0_le_Sing' m, C0_pos]

/-- (3.3), the second inequality: for `m ≥ X/2`, `X^{1-ε}/4 < m 𝔖(m) / (2 X^ε)` once
`C₀ > 1/2`; the numeric value `C₀ = 0.66016...` of (2.4) gives it. -/
theorem eq33 (hC : 1 / 2 < C0) {X : ℝ} (hX : 0 < X) (ε : ℝ) (m : ℕ) (hm : X / 2 ≤ m) :
    X ^ (1 - ε) / 4 < m * Sing m / (2 * X ^ ε) := by
  have hXe : 0 < X ^ ε := rpow_pos_of_pos hX ε
  have hsplit : X ^ (1 - ε) = X / X ^ ε := by rw [rpow_sub hX, rpow_one]
  rw [hsplit, lt_div_iff₀ (by positivity)]
  have hS := two_C0_le_Sing' m
  have h1 : X / X ^ ε / 4 * (2 * X ^ ε) = X / 2 := by field_simp; ring
  rw [h1]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-! ### Counting lemmas -/

/-- Chebyshev's inequality, second moment. -/
theorem card_filter_le_sum_sq (s : Finset ℕ) (f : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    ((s.filter (fun m => T ≤ f m)).card : ℝ) ≤ (∑ m ∈ s, f m ^ 2) / T ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  calc ((s.filter (fun m => T ≤ f m)).card : ℝ) * T ^ 2
      = ∑ m ∈ s.filter (fun m => T ≤ f m), T ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ s.filter (fun m => T ≤ f m), f m ^ 2 := by
        apply sum_le_sum; intro m hm
        exact pow_le_pow_left₀ hT.le (mem_filter.mp hm).2 2
    _ ≤ ∑ m ∈ s, f m ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- Chebyshev's inequality, first moment, for `f ≥ 0`. -/
theorem card_filter_le_sum (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ m ∈ s, 0 ≤ f m) {T : ℝ}
    (hT : 0 < T) : ((s.filter (fun m => T ≤ f m)).card : ℝ) ≤ (∑ m ∈ s, f m) / T := by
  rw [le_div_iff₀ hT]
  calc ((s.filter (fun m => T ≤ f m)).card : ℝ) * T
      = ∑ m ∈ s.filter (fun m => T ≤ f m), T := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ s.filter (fun m => T ≤ f m), f m := by
        apply sum_le_sum; intro m hm; exact (mem_filter.mp hm).2
    _ ≤ ∑ m ∈ s, f m :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun m hm _ => hf m hm)

/-- `#{m ∈ (0, N] : r ∣ C m} ≤ C N / r`, through the injection `m ↦ C m`. -/
theorem card_dvd_mul_nat (r C N : ℕ) (hC : 0 < C) :
    ((Ioc 0 N).filter (fun m => r ∣ C * m)).card ≤ C * N / r := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card_of_injOn (fun m => C * m)
  · intro m hm
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hm ⊢
    exact ⟨⟨Nat.mul_pos hC hm.1.1, Nat.mul_le_mul_left C hm.1.2⟩, hm.2⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hC h

/-- Case 1 of Section 3: the `m ≤ N` with `R ∣ C m` number at most `C N / R`. -/
theorem card_dvd_mul_le (R C N : ℕ) (_hR : 0 < R) (hC : 0 < C) :
    (((Ioc 0 N).filter (fun m => R ∣ C * m)).card : ℝ) ≤ C * N / R := by
  have h := card_dvd_mul_nat R C N hC
  calc (((Ioc 0 N).filter (fun m => R ∣ C * m)).card : ℝ) ≤ ((C * N / R : ℕ) : ℝ) := by
        exact_mod_cast h
    _ ≤ ((C * N : ℕ) : ℝ) / R := Nat.cast_div_le
    _ = C * N / R := by push_cast; ring

/-- `{x : ℤ | R ∣ x²}` is an ideal of `ℤ`. -/
def sqIdeal (R : ℤ) : Ideal ℤ where
  carrier := {x | R ∣ x ^ 2}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    have hab : R ∣ a * b := by
      have : R ^ 2 ∣ (a * b) ^ 2 := by rw [mul_pow, sq R]; exact mul_dvd_mul ha hb
      exact (Int.pow_dvd_pow_iff two_ne_zero).mp this
    have : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
    rw [this]
    exact dvd_add (dvd_add ha (dvd_mul_of_dvd_right hab 2)) hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [mul_pow]; exact dvd_mul_of_dvd_right hx _

/-- For `R > 0` there is `r > 0` with `R ∣ r²` and `R ∣ m² → r ∣ m`: the generator of
`sqIdeal R`. -/
theorem exists_sq_gen (R : ℕ) (_hR : 0 < R) :
    ∃ r : ℕ, 0 < r ∧ R ∣ r ^ 2 ∧ ∀ m : ℕ, R ∣ m ^ 2 → r ∣ m := by
  set I := sqIdeal (R : ℤ)
  set g := Submodule.IsPrincipal.generator I
  have hmem : ∀ x : ℤ, x ∈ I ↔ g ∣ x := by
    intro x
    rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
  have hg : (R : ℤ) ∣ g ^ 2 := Submodule.IsPrincipal.generator_mem I
  have hdiv : ∀ m : ℕ, R ∣ m ^ 2 → g.natAbs ∣ m := by
    intro m hm
    have : (m : ℤ) ∈ I := by
      show (R : ℤ) ∣ (m : ℤ) ^ 2
      exact_mod_cast hm
    have h2 := (hmem _).mp this
    have := Int.natAbs_dvd_natAbs.mpr h2
    simpa using this
  refine ⟨g.natAbs, ?_, ?_, hdiv⟩
  · have hRR : R ∣ R ^ 2 := dvd_pow_self R two_ne_zero
    have := hdiv R hRR
    rcases Nat.eq_zero_or_pos g.natAbs with h0 | h0
    · rw [h0, zero_dvd_iff] at this; omega
    · exact h0
  · have h3 : (R : ℤ) ∣ ((g.natAbs ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Int.natAbs_sq]; exact hg
    exact_mod_cast h3

/-- (5.14) and (5.15): the `m ≤ N` with `R ∣ C m²` number at most `C N / √R`. -/
theorem card_dvd_mul_sq_le (R C N : ℕ) (hR : 0 < R) (hC : 0 < C) :
    (((Ioc 0 N).filter (fun m => R ∣ C * m ^ 2)).card : ℝ) ≤ C * N / Real.sqrt R := by
  obtain ⟨r, hr0, hRr, hdiv⟩ := exists_sq_gen R hR
  have hsub : (Ioc 0 N).filter (fun m => R ∣ C * m ^ 2) ⊆ (Ioc 0 N).filter (fun m => r ∣ C * m) := by
    intro m hm
    simp only [mem_filter] at hm ⊢
    refine ⟨hm.1, hdiv _ ?_⟩
    have : C * m ^ 2 ∣ (C * m) ^ 2 := ⟨C, by ring⟩
    exact hm.2.trans this
  have h1 := card_dvd_mul_le r C N hr0 hC
  have hcard : (((Ioc 0 N).filter (fun m => R ∣ C * m ^ 2)).card : ℝ) ≤
      (((Ioc 0 N).filter (fun m => r ∣ C * m)).card : ℝ) := by exact_mod_cast card_le_card hsub
  have hRle : (R : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast Nat.le_of_dvd (by positivity) hRr
  have hsq : Real.sqrt R ≤ r := by
    rw [Real.sqrt_le_left (by positivity)]; exact hRle
  have hsqpos : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by exact_mod_cast hR)
  have hnum : (0 : ℝ) ≤ C * N := by positivity
  calc _ ≤ (C * N : ℝ) / r := hcard.trans h1
    _ ≤ C * N / Real.sqrt R := div_le_div_of_nonneg_left hnum hsqpos hsq

/-! ### The counting step of Sections 3 and 5 -/

/-- From `R = R₁ + R₂`: if `Re R(m) > 0` forces `good m`, then outside the major arc
exceptions, those `m` with `Re R₁(m) ≤ T`, every bad `m` has `|R₂(m)| ≥ T`. -/
theorem bad_subset {s : Finset ℕ} {good : ℕ → Prop} (R1 R2 : ℕ → ℂ) (T : ℝ)
    (bad1 : Finset ℕ) (hGold : ∀ m ∈ s, 0 < (R1 m + R2 m).re → good m)
    (hMajor : ∀ m ∈ s, (R1 m).re ≤ T → m ∈ bad1) :
    s.filter (fun m => ¬ good m) ⊆ bad1 ∪ s.filter (fun m => T ≤ ‖R2 m‖) := by
  intro m hm
  obtain ⟨hs, hg⟩ := mem_filter.mp hm
  rw [mem_union]
  by_cases h1 : (R1 m).re ≤ T
  · exact Or.inl (hMajor m hs h1)
  · right
    refine mem_filter.mpr ⟨hs, ?_⟩
    by_contra h2
    push Not at h1 h2
    have hre := (abs_le.mp (Complex.abs_re_le_norm (R2 m))).1
    exact hg (hGold m hs (by rw [Complex.add_re]; linarith))

/-- Section 3, (3.1) to (3.3): the second moment of `R₂` bounds the minor arc exceptions. -/
theorem block_count_sq {s : Finset ℕ} {good : ℕ → Prop} (R1 R2 : ℕ → ℂ) {T B : ℝ}
    (hT : 0 < T) (bad1 : Finset ℕ) (hGold : ∀ m ∈ s, 0 < (R1 m + R2 m).re → good m)
    (hMinor : ∑ m ∈ s, ‖R2 m‖ ^ 2 ≤ B) (hMajor : ∀ m ∈ s, (R1 m).re ≤ T → m ∈ bad1) :
    ((s.filter (fun m => ¬ good m)).card : ℝ) ≤ bad1.card + B / T ^ 2 := by
  have h1 := card_le_card (bad_subset R1 R2 T bad1 hGold hMajor)
  have h2 := card_union_le bad1 (s.filter (fun m => T ≤ ‖R2 m‖))
  have h3 := card_filter_le_sum_sq s (fun m => ‖R2 m‖) hT
  have h4 : (∑ m ∈ s, ‖R2 m‖ ^ 2) / T ^ 2 ≤ B / T ^ 2 :=
    div_le_div_of_nonneg_right hMinor (by positivity)
  have h12 : ((s.filter (fun m => ¬ good m)).card : ℝ) ≤
      bad1.card + (s.filter (fun m => T ≤ ‖R2 m‖)).card := by exact_mod_cast h1.trans h2
  linarith

/-- Section 5, (5.11) to (5.13): the first moment of `R₂` bounds the minor arc exceptions. -/
theorem block_count_abs {s : Finset ℕ} {good : ℕ → Prop} (R1 R2 : ℕ → ℂ) {T B : ℝ}
    (hT : 0 < T) (bad1 : Finset ℕ) (hGold : ∀ m ∈ s, 0 < (R1 m + R2 m).re → good m)
    (hMinor : ∑ m ∈ s, ‖R2 m‖ ≤ B) (hMajor : ∀ m ∈ s, (R1 m).re ≤ T → m ∈ bad1) :
    ((s.filter (fun m => ¬ good m)).card : ℝ) ≤ bad1.card + B / T := by
  have h1 := card_le_card (bad_subset R1 R2 T bad1 hGold hMajor)
  have h2 := card_union_le bad1 (s.filter (fun m => T ≤ ‖R2 m‖))
  have h3 := card_filter_le_sum s (fun m => ‖R2 m‖) (fun m _ => norm_nonneg _) hT
  have h4 : (∑ m ∈ s, ‖R2 m‖) / T ≤ B / T := div_le_div_of_nonneg_right hMinor hT.le
  have h12 : ((s.filter (fun m => ¬ good m)).card : ℝ) ≤
      bad1.card + (s.filter (fun m => T ≤ ‖R2 m‖)).card := by exact_mod_cast h1.trans h2
  linarith

/-- Union bound over the Case 1 moduli. -/
theorem card_classes_le {s : Finset ℕ} (𝓡 : Finset ℕ) (P : ℕ → ℕ → Prop)
    [∀ R0, DecidablePred (P R0)] {b : ℝ}
    (hb : ∀ R0 ∈ 𝓡, ((s.filter (fun m => P R0 m)).card : ℝ) ≤ b) :
    ((s.filter (fun m => ∃ R0 ∈ 𝓡, P R0 m)).card : ℝ) ≤ 𝓡.card * b := by
  have hsub : s.filter (fun m => ∃ R0 ∈ 𝓡, P R0 m) ⊆ 𝓡.biUnion (fun R0 => s.filter (P R0)) := by
    intro m hm
    obtain ⟨hs, R0, hR0, hP⟩ := mem_filter.mp hm
    exact mem_biUnion.mpr ⟨R0, hR0, mem_filter.mpr ⟨hs, hP⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  calc ((s.filter (fun m => ∃ R0 ∈ 𝓡, P R0 m)).card : ℝ)
      ≤ ((∑ R0 ∈ 𝓡, (s.filter (P R0)).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ R0 ∈ 𝓡, ((s.filter (P R0)).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _R0 ∈ 𝓡, b := sum_le_sum hb
    _ = 𝓡.card * b := by rw [sum_const, nsmul_eq_mul]

/-! ### Logarithms against powers -/

/-- `(log x)^k ≤ A x^δ` for `x ≥ 1`, any `δ > 0`. -/
theorem log_pow_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → Real.log x ^ k ≤ A * x ^ δ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [hk, pow_zero, one_mul]; exact one_le_rpow hx hδ.le
  · set η : ℝ := δ / k with hη
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hηpos : 0 < η := div_pos hδ hkpos
    refine ⟨1 / η ^ k, by positivity, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have h1 : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div hx0 hηpos
    calc Real.log x ^ k ≤ (x ^ η / η) ^ k := pow_le_pow_left₀ hlog0 h1 k
      _ = 1 / η ^ k * (x ^ η) ^ k := by rw [div_pow]; ring
      _ = 1 / η ^ k * x ^ δ := by
          rw [← rpow_mul_natCast hx0, hη, div_mul_cancel₀ _ hkpos.ne']

/-! ### Section 3: Theorem 3 from the inputs -/

/-- The inputs of Section 3 at level `ε`, with `P = Y^{7/25}` on the block `(⌊Y/2⌋, Y]`, for all
`Y > Y₀`. `R₁`, `R₂` are the major and minor arc parts (1.7), (1.8) of `R(m)`.
* (1.6): for even `m`, `Re R(m) > 0` gives `m = p + p'`.
* (3.1): `∑_m |R₂(m)|² ≤ K X³ L^k / P`, Parseval with Lemma 1, `L = log X`. The paper prints
  `k = 5`; squaring the `L⁴` of (1.10) gives `k = 9`, so any `k` is allowed here.
* (3.5) in the Siegel case, (3.6) with Theorem 2 in Case 2: `Re R₁(m) > X^{1-ε}` unless `m`
  lies in a Case 1 class `R₀ ∣ C m`, with `R₀ ≥ P`, at most `M` classes by (2.3).
`threshold_of_36` shows that (3.6), `R₁(m) > ε m 𝔖(m)`, implies the threshold `X^{1-ε}`. -/
def Section3Input (ε : ℝ) : Prop :=
  ∃ (K : ℝ) (k C M Y0 : ℕ), 0 < C ∧ ∀ Y : ℕ, Y0 < Y → ∃ (R1 R2 : ℕ → ℂ) (𝓡 : Finset ℕ),
    (∀ m ∈ Ioc (Y / 2) Y, Even m → 0 < (R1 m + R2 m).re → IsGoldbachSum m) ∧
    ∑ m ∈ Ioc (Y / 2) Y, ‖R2 m‖ ^ 2 ≤ K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ (7 / 25 : ℝ) ∧
    (∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 m).re ≤ (Y : ℝ) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m) ∧
    (∀ R0 ∈ 𝓡, (Y : ℝ) ^ (7 / 25 : ℝ) ≤ R0) ∧ 𝓡.card ≤ M

/-- (3.6) gives the threshold: for large `Y` and `m > Y/2`, `Y^{1-ε} < ε m 𝔖(m)`. -/
theorem threshold_of_36 {ε : ℝ} (hε : 0 < ε) :
    ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → ∀ m : ℕ, (Y : ℝ) / 2 ≤ m →
      (Y : ℝ) ^ (1 - ε) < ε * m * Sing m := by
  have ht : Tendsto (fun Y : ℕ => (Y : ℝ) ^ (-ε)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  have hc : 0 < ε * C0 := mul_pos hε C0_pos
  obtain ⟨Y1, hY1⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
  refine ⟨Y1, fun Y hY m hm => ?_⟩
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hs := hY1 Y hY.le
  have hsplit : (Y : ℝ) ^ (1 - ε) = (Y : ℝ) ^ (-ε) * Y := by
    rw [show (1 - ε) = -ε + 1 by ring, rpow_add hYpos, rpow_one]
  have hS := two_C0_le_Sing' m
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hsplit]
  have h1 : (Y : ℝ) ^ (-ε) * Y < ε * C0 * Y := mul_lt_mul_of_pos_right hs hYpos
  have h2 : ε * C0 * Y ≤ ε * m * Sing m := by
    have : C0 * Y ≤ m * Sing m := by nlinarith [C0_pos]
    nlinarith
  linarith

/-- The block exponent arithmetic: `Y³ / Y^{7/25} / (Y^{1-ε})² = Y^{18/25 + 2ε}`. -/
theorem block_exponent {y : ℝ} (hy : 0 < y) (ε : ℝ) :
    y ^ 3 / y ^ (7 / 25 : ℝ) / (y ^ (1 - ε)) ^ 2 = y ^ (18 / 25 + 2 * ε : ℝ) := by
  rw [← rpow_natCast, ← rpow_natCast (y ^ (1 - ε)), ← rpow_mul hy.le, ← rpow_sub hy,
    ← rpow_sub hy]
  congr 1; push_cast; ring

/-- One block: `D Exc Y ≤ M C Y / Y^{7/25} + K Y^{18/25+2ε} (log Y)^k`. -/
theorem block_bound {ε K : ℝ} {k C M Y : ℕ} (hC : 0 < C) (hY : 0 < Y) (R1 R2 : ℕ → ℂ)
    (𝓡 : Finset ℕ)
    (hGold : ∀ m ∈ Ioc (Y / 2) Y, Even m → 0 < (R1 m + R2 m).re → IsGoldbachSum m)
    (hMinor : ∑ m ∈ Ioc (Y / 2) Y, ‖R2 m‖ ^ 2 ≤
      K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ (7 / 25 : ℝ))
    (hMajor : ∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 m).re ≤ (Y : ℝ) ^ (1 - ε) →
      ∃ R0 ∈ 𝓡, R0 ∣ C * m)
    (hP : ∀ R0 ∈ 𝓡, (Y : ℝ) ^ (7 / 25 : ℝ) ≤ R0) (hM : 𝓡.card ≤ M) :
    (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      M * (C * Y / (Y : ℝ) ^ (7 / 25 : ℝ)) +
        K * Real.log Y ^ k * (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ) := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hPpos : 0 < (Y : ℝ) ^ (7 / 25 : ℝ) := rpow_pos_of_pos hYr _
  set s := (Ioc (Y / 2) Y).filter Even
  set T : ℝ := (Y : ℝ) ^ (1 - ε)
  have hT : 0 < T := rpow_pos_of_pos hYr _
  set bad1 := s.filter (fun m => ∃ R0 ∈ 𝓡, R0 ∣ C * m)
  have hcount := block_count_sq (s := s) (good := IsGoldbachSum) R1 R2 hT bad1
    (fun m hm => hGold m (mem_filter.mp hm).1 (mem_filter.mp hm).2)
    ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans hMinor)
    (fun m hm h => mem_filter.mpr ⟨hm, hMajor m (mem_filter.mp hm).1 (mem_filter.mp hm).2 h⟩)
  -- D Exc Y is at most the count of the non-Goldbach even `m` in the block
  have hD : (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      ((s.filter (fun m => ¬ IsGoldbachSum m)).card : ℝ) := by
    unfold Pintz2018Reduction.D Pintz2018Reduction.Exc
    exact_mod_cast card_le_card (fun m hm => by
      simp only [s, mem_filter] at hm ⊢
      exact ⟨⟨hm.1, hm.2.2.1⟩, hm.2.2.2⟩)
  -- the Case 1 classes
  have hclass : ∀ R0 ∈ 𝓡, ((s.filter (fun m => R0 ∣ C * m)).card : ℝ) ≤
      C * Y / (Y : ℝ) ^ (7 / 25 : ℝ) := by
    intro R0 hR0
    have hR0pos : (0 : ℝ) < R0 := lt_of_lt_of_le hPpos (hP R0 hR0)
    have hsub : s.filter (fun m => R0 ∣ C * m) ⊆ (Ioc 0 Y).filter (fun m => R0 ∣ C * m) := by
      intro m hm
      simp only [s, mem_filter, mem_Ioc] at hm ⊢
      exact ⟨⟨by omega, hm.1.1.2⟩, hm.2⟩
    have h1 := card_dvd_mul_le R0 C Y (by exact_mod_cast hR0pos) hC
    have h2 : (C : ℝ) * Y / R0 ≤ C * Y / (Y : ℝ) ^ (7 / 25 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hPpos (hP R0 hR0)
    calc ((s.filter (fun m => R0 ∣ C * m)).card : ℝ)
        ≤ (((Ioc 0 Y).filter (fun m => R0 ∣ C * m)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ _ := h1.trans h2
  have hbad1 : (bad1.card : ℝ) ≤ M * (C * Y / (Y : ℝ) ^ (7 / 25 : ℝ)) := by
    have := card_classes_le (s := s) 𝓡 (fun R0 m => R0 ∣ C * m) hclass
    have hMr : (𝓡.card : ℝ) ≤ M := by exact_mod_cast hM
    calc (bad1.card : ℝ) ≤ 𝓡.card * (C * Y / (Y : ℝ) ^ (7 / 25 : ℝ)) := this
      _ ≤ M * (C * Y / (Y : ℝ) ^ (7 / 25 : ℝ)) :=
          mul_le_mul_of_nonneg_right hMr (by positivity)
  have hB : K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ (7 / 25 : ℝ) / T ^ 2 =
      K * Real.log Y ^ k * (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ) := by
    rw [← block_exponent hYr ε]; ring
  linarith

/-- CONDITIONAL ON `Section3Input ε`: the blocks satisfy `D Exc Y ≤ A Y^{0.72+3ε}`. -/
theorem blocks_of_section3Input {ε : ℝ} (hε : 0 < ε) (h : Section3Input ε) :
    ∃ (A : ℝ) (Y0 : ℕ), 0 ≤ A ∧ ∀ Y : ℕ, Y0 < Y →
      (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤ A * (Y : ℝ) ^ (0.72 + 3 * ε) := by
  obtain ⟨K, k, C, M, Y0, hC, hin⟩ := h
  obtain ⟨A1, hA1, hlog⟩ := log_pow_le k hε
  refine ⟨M * C + |K| * A1, Y0, by positivity, fun Y hY => ?_⟩
  obtain ⟨R1, R2, 𝓡, hG, hMi, hMa, hP, hM⟩ := hin Y hY
  have hY0 : 0 < Y := by omega
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY0
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY0
  have hb := block_bound hC hY0 R1 R2 𝓡 hG hMi hMa hP hM
  -- first term
  have hfirst : (C : ℝ) * Y / (Y : ℝ) ^ (7 / 25 : ℝ) ≤ C * (Y : ℝ) ^ (0.72 + 3 * ε) := by
    have hYe : (Y : ℝ) / (Y : ℝ) ^ (7 / 25 : ℝ) = (Y : ℝ) ^ (0.72 : ℝ) := by
      rw [div_eq_iff (rpow_pos_of_pos hYr _).ne', ← rpow_add hYr]
      norm_num
    have hmono : (Y : ℝ) ^ (0.72 : ℝ) ≤ (Y : ℝ) ^ (0.72 + 3 * ε) :=
      rpow_le_rpow_of_exponent_le hY1 (by linarith)
    rw [mul_div_assoc, hYe]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  -- second term
  have hsecond : K * Real.log Y ^ k * (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ) ≤
      |K| * A1 * (Y : ℝ) ^ (0.72 + 3 * ε) := by
    have hl := hlog Y hY1
    have hl0 : 0 ≤ Real.log Y ^ k := pow_nonneg (Real.log_nonneg hY1) k
    have hYa : 0 ≤ (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ) := rpow_nonneg hYr.le _
    have hsplit : (Y : ℝ) ^ (0.72 + 3 * ε) = (Y : ℝ) ^ ε * (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ) := by
      rw [← rpow_add hYr]; congr 1; norm_num; ring
    calc K * Real.log Y ^ k * (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ)
        ≤ |K| * Real.log Y ^ k * (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hYa
          exact mul_le_mul_of_nonneg_right (le_abs_self K) hl0
      _ ≤ |K| * (A1 * (Y : ℝ) ^ ε) * (Y : ℝ) ^ (18 / 25 + 2 * ε : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hYa
          exact mul_le_mul_of_nonneg_left hl (abs_nonneg K)
      _ = |K| * A1 * (Y : ℝ) ^ (0.72 + 3 * ε) := by rw [hsplit]; ring
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have : (M : ℝ) * (C * Y / (Y : ℝ) ^ (7 / 25 : ℝ)) ≤ M * (C * (Y : ℝ) ^ (0.72 + 3 * ε)) :=
    mul_le_mul_of_nonneg_left hfirst hMr
  nlinarith

/-- CONDITIONAL ON `Section3Input ε`: `E(X) ≪ X^{0.72+3ε}`. -/
theorem powerBound_of_section3Input {ε : ℝ} (hε : 0 < ε) (h : Section3Input ε) :
    PowerBound (0.72 + 3 * ε) := by
  obtain ⟨A, Y0, hA, hD⟩ := blocks_of_section3Input hε h
  have hα : (0 : ℝ) < 0.72 + 3 * ε := by linarith
  set r : ℝ := (2 : ℝ) ^ (-(0.72 + 3 * ε))
  have hr1 : r < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨A / (1 - r) + Pintz2018Reduction.T Pintz2018Reduction.Exc Y0, fun X hX => ?_⟩
  have hb := Pintz2018Reduction.T_le Pintz2018Reduction.Exc hα hA hD X
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXa : 1 ≤ (X : ℝ) ^ (0.72 + 3 * ε) := one_le_rpow hX1 hα.le
  have hT0 : (0 : ℝ) ≤ Pintz2018Reduction.T Pintz2018Reduction.Exc Y0 := Nat.cast_nonneg _
  rw [Pintz2018Reduction.E_eq_T]
  have : (Pintz2018Reduction.T Pintz2018Reduction.Exc Y0 : ℝ) ≤
      Pintz2018Reduction.T Pintz2018Reduction.Exc Y0 * (X : ℝ) ^ (0.72 + 3 * ε) := by
    nlinarith
  calc (Pintz2018Reduction.T Pintz2018Reduction.Exc X : ℝ)
      ≤ A / (1 - r) * (X : ℝ) ^ (0.72 + 3 * ε) +
          Pintz2018Reduction.T Pintz2018Reduction.Exc Y0 := hb
    _ ≤ _ := by rw [add_mul]; linarith

/-- CONDITIONAL ON `Section3Input ε` for every `ε > 0`: Theorem 3 of the paper. -/
theorem theorem3_of_section3Input (h : ∀ ε : ℝ, 0 < ε → Section3Input ε) :
    LeanLab.ExceptionalSet.Pintz2021.Theorem3 := by
  intro ε hε
  have := powerBound_of_section3Input (ε := ε / 3) (by linarith) (h (ε / 3) (by linarith))
  rwa [show (0.72 : ℝ) + 3 * (ε / 3) = 0.72 + ε by ring] at this

/-! ### Section 5: Theorem 5 from the inputs -/

/-- (5.11): with `X = N²`, `X^{2/5} X^{3/4} N^{1/2} = X N^{4/5}`, the Hölder exponents. -/
theorem holder_511 {N : ℝ} (hN : 0 < N) :
    (N ^ 2) ^ (2 / 5 : ℝ) * (N ^ 2) ^ (3 / 4 : ℝ) * N ^ (1 / 2 : ℝ) = N ^ 2 * N ^ (4 / 5 : ℝ) := by
  rw [← rpow_natCast N 2, ← rpow_mul hN.le, ← rpow_mul hN.le, ← rpow_add hN, ← rpow_add hN,
    ← rpow_add hN]
  congr 1; push_cast; ring

/-- The inputs of Section 5 at level `ε` for all `N > N₀`, with `X = N²` and `P* = X^{7/25}`.
`R₁`, `R₂` are the major and minor arc parts of `R(2m²)`.
* (1.6): `Re R(2m²) > 0` gives `2m² = p + p'`.
* (5.11): `∑_{m ≤ N} |R₂(2m²)| ≤ K X N^{4/5} L^c`, `L = log X`.
* (5.16) with Theorem 2 in Case 2, and (3.5) for the Siegel case: `Re R₁(2m²) > X^{1-ε}` unless
  `m` lies in a Case 1 class (5.14), `R₀ ∣ C m²` with `R₀ ≥ P*`, at most `M` classes. -/
def Section5Input (ε : ℝ) : Prop :=
  ∃ (K : ℝ) (c C M N0 : ℕ), 0 < C ∧ ∀ N : ℕ, N0 < N → ∃ (R1 R2 : ℕ → ℂ) (𝓡 : Finset ℕ),
    (∀ m ∈ Icc 1 N, 0 < (R1 m + R2 m).re → IsGoldbachSum (2 * m ^ 2)) ∧
    ∑ m ∈ Icc 1 N, ‖R2 m‖ ≤ K * (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) * Real.log ((N : ℝ) ^ 2) ^ c ∧
    (∀ m ∈ Icc 1 N, (R1 m).re ≤ ((N : ℝ) ^ 2) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m ^ 2) ∧
    (∀ R0 ∈ 𝓡, ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) ≤ R0) ∧ 𝓡.card ≤ M

theorem Icc_one_eq_Ioc (N : ℕ) : Icc 1 N = Ioc 0 N := by ext m; simp; omega

/-- One `N`: `E₂(N) ≤ M C N^{18/25} + K N^{4/5+2ε} (log N²)^c`. -/
theorem sq_bound {ε K : ℝ} {c C M N : ℕ} (hC : 0 < C) (hN : 0 < N) (R1 R2 : ℕ → ℂ)
    (𝓡 : Finset ℕ)
    (hGold : ∀ m ∈ Icc 1 N, 0 < (R1 m + R2 m).re → IsGoldbachSum (2 * m ^ 2))
    (hMinor : ∑ m ∈ Icc 1 N, ‖R2 m‖ ≤
      K * (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) * Real.log ((N : ℝ) ^ 2) ^ c)
    (hMajor : ∀ m ∈ Icc 1 N, (R1 m).re ≤ ((N : ℝ) ^ 2) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m ^ 2)
    (hP : ∀ R0 ∈ 𝓡, ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) ≤ R0) (hM : 𝓡.card ≤ M) :
    (LeanLab.ExceptionalSet.Pintz2021.EPoly 2 N : ℝ) ≤
      M * (C * (N : ℝ) ^ (18 / 25 : ℝ)) +
        K * Real.log ((N : ℝ) ^ 2) ^ c * (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hPeq : ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) = (N : ℝ) ^ (14 / 25 : ℝ) := by
    rw [← rpow_natCast N 2, ← rpow_mul hNr.le]; norm_num
  have hPpos : 0 < ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) := rpow_pos_of_pos hX _
  set s := Icc 1 N
  set T : ℝ := ((N : ℝ) ^ 2) ^ (1 - ε)
  have hT : 0 < T := rpow_pos_of_pos hX _
  set bad1 := s.filter (fun m => ∃ R0 ∈ 𝓡, R0 ∣ C * m ^ 2)
  have hcount := block_count_abs (s := s) (good := fun m => IsGoldbachSum (2 * m ^ 2)) R1 R2 hT
    bad1 hGold hMinor (fun m hm h => mem_filter.mpr ⟨hm, hMajor m hm h⟩)
  have hE : (LeanLab.ExceptionalSet.Pintz2021.EPoly 2 N : ℝ) =
      ((s.filter (fun m => ¬ IsGoldbachSum (2 * m ^ 2))).card : ℝ) := by
    unfold LeanLab.ExceptionalSet.Pintz2021.EPoly; congr
  have hclass : ∀ R0 ∈ 𝓡, ((s.filter (fun m => R0 ∣ C * m ^ 2)).card : ℝ) ≤
      C * (N : ℝ) ^ (18 / 25 : ℝ) := by
    intro R0 hR0
    have hR0pos : (0 : ℝ) < R0 := lt_of_lt_of_le hPpos (hP R0 hR0)
    have h1 := card_dvd_mul_sq_le R0 C N (by exact_mod_cast hR0pos) hC
    have hsq : (N : ℝ) ^ (7 / 25 : ℝ) ≤ Real.sqrt R0 := by
      rw [Real.le_sqrt (by positivity) hR0pos.le, ← rpow_natCast, ← rpow_mul hNr.le]
      have := hP R0 hR0; rw [hPeq] at this; norm_num at this ⊢; exact this
    have hNpos : 0 < (N : ℝ) ^ (7 / 25 : ℝ) := rpow_pos_of_pos hNr _
    have h2 : (C : ℝ) * N / Real.sqrt R0 ≤ C * N / (N : ℝ) ^ (7 / 25 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hNpos hsq
    have h3 : (C : ℝ) * N / (N : ℝ) ^ (7 / 25 : ℝ) = C * (N : ℝ) ^ (18 / 25 : ℝ) := by
      rw [mul_div_assoc]; congr 1
      rw [div_eq_iff hNpos.ne', ← rpow_add hNr]; norm_num
    calc ((s.filter (fun m => R0 ∣ C * m ^ 2)).card : ℝ) ≤ C * N / Real.sqrt R0 := by
          rw [show s = Ioc 0 N from Icc_one_eq_Ioc N]; exact h1
      _ ≤ _ := h2.trans h3.le
  have hbad1 : (bad1.card : ℝ) ≤ M * (C * (N : ℝ) ^ (18 / 25 : ℝ)) := by
    have := card_classes_le (s := s) 𝓡 (fun R0 m => R0 ∣ C * m ^ 2) hclass
    have hMr : (𝓡.card : ℝ) ≤ M := by exact_mod_cast hM
    calc (bad1.card : ℝ) ≤ 𝓡.card * (C * (N : ℝ) ^ (18 / 25 : ℝ)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_right hMr (by positivity)
  have hB : K * (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) * Real.log ((N : ℝ) ^ 2) ^ c / T =
      K * Real.log ((N : ℝ) ^ 2) ^ c * (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) := by
    have hTe : T = (N : ℝ) ^ (2 - 2 * ε) := by
      simp only [T]; rw [← rpow_natCast N 2, ← rpow_mul hNr.le]; congr 1; push_cast; ring
    have hpow : (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) / (N : ℝ) ^ (2 - 2 * ε) =
        (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) := by
      rw [← rpow_natCast N 2, ← rpow_add hNr, ← rpow_sub hNr]; congr 1; push_cast; ring
    rw [hTe, ← hpow]; ring
  rw [hE]; linarith

/-- CONDITIONAL ON `Section5Input ε`: `E₂(N) ≪ N^{4/5+3ε}`. -/
theorem polyPowerBound_of_section5Input {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (h : Section5Input ε) :
    LeanLab.ExceptionalSet.Pintz2021.PolyPowerBound 2 (4 / 5 + 3 * ε) := by
  obtain ⟨K, c, C, M, N0, hC, hin⟩ := h
  obtain ⟨A1, hA1, hlog⟩ := log_pow_le c hε
  refine ⟨M * C + |K| * (2 ^ c * A1) + N0, fun N hN => ?_⟩
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by linarith
  have hθ : (0 : ℝ) ≤ 4 / 5 + 3 * ε := by linarith
  have hNa : 1 ≤ (N : ℝ) ^ (4 / 5 + 3 * ε) := one_le_rpow hNr1 hθ
  have hMC : (0 : ℝ) ≤ M * C := by positivity
  have hKA : (0 : ℝ) ≤ |K| * (2 ^ c * A1) := by positivity
  rcases le_or_gt N N0 with hNN | hNN
  · -- small `N`: the trivial bound `E₂(N) ≤ N ≤ N₀`
    have h1 : (LeanLab.ExceptionalSet.Pintz2021.EPoly 2 N : ℝ) ≤ N0 := by
      exact_mod_cast (LeanLab.ExceptionalSet.Pintz2021.EPoly_le 2 N).trans hNN
    have hN0 : (0 : ℝ) ≤ N0 := Nat.cast_nonneg N0
    nlinarith
  · obtain ⟨R1, R2, 𝓡, hG, hMi, hMa, hP, hM⟩ := hin N hNN
    have hb := sq_bound hC (by omega) R1 R2 𝓡 hG hMi hMa hP hM
    have hfirst : (N : ℝ) ^ (18 / 25 : ℝ) ≤ (N : ℝ) ^ (4 / 5 + 3 * ε) :=
      rpow_le_rpow_of_exponent_le hNr1 (by linarith)
    have hlogN : Real.log ((N : ℝ) ^ 2) ^ c ≤ 2 ^ c * A1 * (N : ℝ) ^ ε := by
      rw [Real.log_pow, mul_pow]; push_cast
      have := hlog N hNr1
      have h2c : (0 : ℝ) ≤ 2 ^ c := by positivity
      calc (2 : ℝ) ^ c * Real.log N ^ c ≤ 2 ^ c * (A1 * (N : ℝ) ^ ε) :=
            mul_le_mul_of_nonneg_left this h2c
        _ = _ := by ring
    have hl0 : 0 ≤ Real.log ((N : ℝ) ^ 2) ^ c :=
      pow_nonneg (Real.log_nonneg (by nlinarith)) c
    have hYa : 0 ≤ (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) := rpow_nonneg hNr.le _
    have hsplit : (N : ℝ) ^ (4 / 5 + 3 * ε) = (N : ℝ) ^ ε * (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) := by
      rw [← rpow_add hNr]; congr 1; ring
    have hsecond : K * Real.log ((N : ℝ) ^ 2) ^ c * (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) ≤
        |K| * (2 ^ c * A1) * (N : ℝ) ^ (4 / 5 + 3 * ε) := by
      calc K * Real.log ((N : ℝ) ^ 2) ^ c * (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ)
          ≤ |K| * Real.log ((N : ℝ) ^ 2) ^ c * (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hYa
            exact mul_le_mul_of_nonneg_right (le_abs_self K) hl0
        _ ≤ |K| * (2 ^ c * A1 * (N : ℝ) ^ ε) * (N : ℝ) ^ (4 / 5 + 2 * ε : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hYa
            exact mul_le_mul_of_nonneg_left hlogN (abs_nonneg K)
        _ = |K| * (2 ^ c * A1) * (N : ℝ) ^ (4 / 5 + 3 * ε) := by rw [hsplit]; ring
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h1 : (M : ℝ) * (C * (N : ℝ) ^ (18 / 25 : ℝ)) ≤ M * C * (N : ℝ) ^ (4 / 5 + 3 * ε) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg C)) hM0
    have hN0 : (0 : ℝ) ≤ N0 := Nat.cast_nonneg N0
    have h3 : (0 : ℝ) ≤ N0 * (N : ℝ) ^ (4 / 5 + 3 * ε) := by positivity
    calc (LeanLab.ExceptionalSet.Pintz2021.EPoly 2 N : ℝ)
        ≤ M * C * (N : ℝ) ^ (4 / 5 + 3 * ε) + |K| * (2 ^ c * A1) * (N : ℝ) ^ (4 / 5 + 3 * ε) := by
          linarith
      _ ≤ (M * C + |K| * (2 ^ c * A1) + N0) * (N : ℝ) ^ (4 / 5 + 3 * ε) := by nlinarith

/-- CONDITIONAL ON `Section5Input ε` for every `ε > 0`: Theorem 5, Perelli and Pintz. -/
theorem theorem5_of_section5Input (h : ∀ ε : ℝ, 0 < ε → Section5Input ε) :
    LeanLab.ExceptionalSet.Pintz2021.Theorem5 := by
  intro ε hε
  have hε' : 0 < min ε 1 / 3 := by positivity
  have := polyPowerBound_of_section5Input hε' (by linarith [min_le_right ε 1])
    (h _ hε')
  exact LeanLab.ExceptionalSet.Pintz2021.polyPowerBound_mono
    (by linarith [min_le_left ε 1]) this

/-! ### Non-vacuity: binary Goldbach satisfies both inputs -/

/-- Sanity check: the inputs are not contradictory, since binary Goldbach, which is OPEN,
implies `Section3Input ε` with `R₁ = Y`, `R₂ = 0` and no Case 1 classes. -/
theorem section3Input_of_binaryGoldbach (hBG : BinaryGoldbach) {ε : ℝ} (hε : 0 < ε) :
    Section3Input ε := by
  refine ⟨0, 0, 1, 0, 8, one_pos, fun Y hY => ⟨fun _ => (Y : ℂ), fun _ => 0, ∅, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro m hm he _
    have := (mem_Ioc.mp hm).1
    exact hBG m he (by omega)
  · simp
  · intro m _ _ h
    exfalso
    have hY1 : (1 : ℝ) < Y := by exact_mod_cast (by omega : 1 < Y)
    have : (Y : ℝ) ^ (1 - ε) < (Y : ℝ) ^ (1 : ℝ) :=
      rpow_lt_rpow_of_exponent_lt hY1 (by linarith)
    rw [rpow_one] at this
    simp at h
    linarith
  · simp
  · simp

/-- Sanity check: binary Goldbach implies `Section5Input ε`. At `m = 1`, `2 = 2·1²` is not a sum
of two primes, so `R₂(1) = -2N²` keeps `Re R(2) < 0`; elsewhere `R₁ = N²`, `R₂ = 0`. -/
theorem section5Input_of_binaryGoldbach (hBG : BinaryGoldbach) {ε : ℝ} (hε : 0 < ε) :
    Section5Input ε := by
  refine ⟨2, 0, 1, 0, 1, one_pos, fun N hN => ⟨fun _ => ((N : ℂ) ^ 2),
    fun m => if m = 1 then -2 * (N : ℂ) ^ 2 else 0, ∅, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro m hm hpos
    have hm1 := (mem_Icc.mp hm).1
    rcases Nat.eq_or_lt_of_le hm1 with h1 | h1
    · exfalso
      subst h1
      simp only [ite_true] at hpos
      have : ((N : ℂ) ^ 2 + -2 * (N : ℂ) ^ 2).re = -((N : ℝ) ^ 2) := by
        simp [pow_two]; ring
      rw [this] at hpos
      nlinarith [sq_nonneg (N : ℝ)]
    · have h4 : 4 ≤ 2 * m ^ 2 := by nlinarith
      exact hBG _ (even_two_mul _) h4
  · have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hsum : ∑ m ∈ Icc 1 N, ‖(if m = 1 then -2 * (N : ℂ) ^ 2 else 0)‖ = 2 * (N : ℝ) ^ 2 := by
      rw [Finset.sum_eq_single 1]
      · simp [norm_pow]
      · intro b _ hb; simp [hb]
      · intro h; exfalso; exact h (mem_Icc.mpr ⟨le_rfl, by omega⟩)
    rw [hsum, pow_zero, mul_one]
    have : (1 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) := one_le_rpow hNr (by norm_num)
    nlinarith [sq_nonneg (N : ℝ)]
  · intro m _ h
    exfalso
    have hN1 : (1 : ℝ) < (N : ℝ) ^ 2 := by
      have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      nlinarith
    have : ((N : ℝ) ^ 2) ^ (1 - ε) < ((N : ℝ) ^ 2) ^ (1 : ℝ) :=
      rpow_lt_rpow_of_exponent_lt hN1 (by linarith)
    rw [rpow_one] at this
    have hre : ((N : ℂ) ^ 2).re = (N : ℝ) ^ 2 := by simp [pow_two]
    rw [hre] at h
    linarith
  · simp
  · simp

end LeanLab.Pintz2021.Applications

-- new
#print axioms LeanLab.Pintz2021.Applications.C0_pos
#print axioms LeanLab.Pintz2021.Applications.Sing_pos
#print axioms LeanLab.Pintz2021.Applications.eq33
#print axioms LeanLab.Pintz2021.Applications.card_dvd_mul_le
#print axioms LeanLab.Pintz2021.Applications.card_dvd_mul_sq_le
#print axioms LeanLab.Pintz2021.Applications.exists_sq_gen
#print axioms LeanLab.Pintz2021.Applications.block_count_sq
#print axioms LeanLab.Pintz2021.Applications.block_count_abs
#print axioms LeanLab.Pintz2021.Applications.card_classes_le
#print axioms LeanLab.Pintz2021.Applications.log_pow_le
#print axioms LeanLab.Pintz2021.Applications.threshold_of_36
#print axioms LeanLab.Pintz2021.Applications.block_exponent
#print axioms LeanLab.Pintz2021.Applications.block_bound
#print axioms LeanLab.Pintz2021.Applications.blocks_of_section3Input
#print axioms LeanLab.Pintz2021.Applications.powerBound_of_section3Input
#print axioms LeanLab.Pintz2021.Applications.theorem3_of_section3Input
#print axioms LeanLab.Pintz2021.Applications.holder_511
#print axioms LeanLab.Pintz2021.Applications.sq_bound
#print axioms LeanLab.Pintz2021.Applications.polyPowerBound_of_section5Input
#print axioms LeanLab.Pintz2021.Applications.theorem5_of_section5Input
#print axioms LeanLab.Pintz2021.Applications.section3Input_of_binaryGoldbach
#print axioms LeanLab.Pintz2021.Applications.section5Input_of_binaryGoldbach
-- VERIFY, rebuilt modules
#print axioms LeanLab.ExceptionalSet.Pintz2021.theorem3_of_theorem3'
#print axioms LeanLab.ExceptionalSet.Pintz2021.EPoly_one_le
#print axioms LeanLab.ExceptionalSet.Pintz2021.EPoly_le_one_of_binaryGoldbach
#print axioms LeanLab.ExceptionalSet.Pintz2021.polyLogPowerSaving_of_polyPowerBound
#print axioms LeanLab.ExceptionalSet.Pintz2021.perelli_two_of_theorem5
#print axioms LeanLab.ExceptionalSet.Pintz2021.polyPowerSaving_two_of_theorem5
#print axioms LeanLab.ExceptionalSet.Pintz2021.polyPowerBound_one_of_powerBound
#print axioms LeanLab.ExceptionalSet.Pintz2021.EPoly_two_eq_one_of_oesilva
#print axioms LeanLab.ExceptionalSet.Pintz2021.EPoly_one_eq_one_of_oesilva
#print axioms LeanLab.ExceptionalSet.Pintz2021.oesilva_two_sharp
#print axioms LeanLab.ExceptionalSet.Pintz2021.perelliPintz
#print axioms LeanLab.Pintz2021.two_C0_le_Sing
#print axioms LeanLab.Pintz2021.Sing_two_pow
#print axioms LeanLab.Pintz2021.N_div_sqrt_P
#print axioms LeanLab.Pintz2021.exponent_517

