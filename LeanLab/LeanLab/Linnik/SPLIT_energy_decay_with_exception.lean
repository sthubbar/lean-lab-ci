/-
Split of `LeanLab.Linnik.Decomp486c.energy_decay_with_exception`.

The sealed statement fixes one exponential decay of the corrected energy in the
exceptional case: for every character `x` of the exceptional family with conductor at most
`P = N ^ θ`, whose L function has a real zero `γ` in the strip below one, the corrected
energy at the conductor `x.1 + 1` and the zero `γ` is at most `C e^{-c/θ}`.

The historical every zero step is `short_interval_mean_decay_exceptional`. It is off the
current route because it needs an unproved fixed strip uniqueness comparison. The
Gallagher window step `energy_window_gallagher` carries the whole statement down to one sum
over primitive characters of conductor at most `P` of the short interval mean square of the
corrected coefficients. That sum is cut here at the one character whose main term is
removed. Only the pair `(x.1, x.2)` of the exceptional family has its principal term
replaced, every other pair keeps the corrected amplitude with no exceptional term, so the
sum splits into the pair `(x.1, x.2)` and the rest, and each piece decays.

Leaves:
* `leaf_sum_split_exceptional`: the finite identity that separates the sum over all pairs
  into the pairs with conductor below `x.1 + 1`, the primitive characters of conductor
  `x.1 + 1` other than `x.2`, and the single pair `(x.1, x.2)`.
* `leaf_exceptional_summand_decay`: CONDITIONAL ON the residual nonmaximal zero leaf
  in Decomp498a. The pair `(x.1, x.2)` alone decays, the removed main
  term leaving a short interval mean square of size at most `C e^{-c/θ} sqrt N / log N`.
* `leaf_nonexceptional_sum_decay`: every other pair together decays with the same shape,
  the zero gap above height `P ^ 5` supplying the exponential saving.
* `leaf_envelope_add`: two exponential envelopes add to one envelope with the smaller rate.

Assembly: `energy_decay_with_exception_split` retains the sealed statement and depends on
the residual nonmaximal zero leaf. The
Gallagher window step, the window length, the real zero and the normalization are the
proved lemmas of the parent file.

Original AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12.
AI proof updates by OpenAI Codex task498, 2026-11-13. Checked by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.Decomp498a

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-- LEAF. The finite split of the character sum at the exceptional pair. With `K` the floor
of `N` to the theta and `γ` the real zero of the exceptional character, the sum over
`k < K` of the primitive character sums of the short interval mean square of the corrected
coefficients at conductor `x.1 + 1` equals the same sum with the conductor `x.1` removed,
plus the primitive characters of conductor `x.1 + 1` other than `x.2`, plus the single
term of the pair `(x.1, x.2)`. Uses only that `x.1 < K` and that `x.2` is primitive. -/
theorem leaf_sum_split_exceptional {N : ℕ} {θ γ : ℝ}
    (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (hK : x.1 < ⌊(N : ℝ) ^ θ⌋₊)
    (hp : x.2.IsPrimitive) :
    (∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          Real.pi / (2 * gallagherLength N θ) *
            Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
              ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                (gallagherLength N θ) m‖ ^ 2))
      = (∑ k ∈ (range ⌊(N : ℝ) ^ θ⌋₊).erase x.1,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2))
        + (∑ χ ∈ ((univ : Finset (DirichletCharacter ℂ (x.1 + 1))).filter
              (fun χ => χ.IsPrimitive)).erase x.2,
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2))
        + (Real.pi / (2 * gallagherLength N θ) *
            Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
              ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient x.2 (x.1 + 1) γ) (N + 1)
                (gallagherLength N θ) m‖ ^ 2)) := by
  classical
  have hxK : x.1 ∈ range ⌊(N : ℝ) ^ θ⌋₊ := mem_range.mpr hK
  have hmem : x.2 ∈ (univ : Finset (DirichletCharacter ℂ (x.1 + 1))).filter
      (fun χ => χ.IsPrimitive) := mem_filter.mpr ⟨mem_univ _, hp⟩
  rw [← sum_erase_add _ _ hxK, ← sum_erase_add _ _ hmem]
  ring

/-- LEAF. The exceptional pair decays on its own. For a primitive character `χ` of
conductor `q + 1` at most `N` to the theta whose L function has a real zero `γ` in the strip
`1 - b / log T` up to one, with `T` equal to `N` to the theta raised to the fifth, the single
summand of the short interval mean square of the corrected coefficients at conductor
`q + 1`, with that real zero removed, is at most `C e^{-c/θ} sqrt N / log N`. This is the
case display 14 handles by replacing the main polynomial of the exceptional character with
the remainder. CONDITIONAL ON leaf_nonmaximal_exceptional_summand_decay for the supplied
zero that is not largest in the sealed strip. The fixed strip question is recorded in
Decomp498a and PROGRESS.md. -/
theorem leaf_exceptional_summand_decay :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (γ : ℝ),
          χ.IsPrimitive → (q : ℝ) + 1 ≤ (N : ℝ) ^ θ → χ.LFunction (γ : ℂ) = 0 →
          1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  obtain ⟨c₁, C₁, θ₁, hc₁, hC₁, hθ₁, hθ₁2, hmaximal⟩ := exceptional_summand_decay_of_max
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hθ₂2, hnonmaximal⟩ :=
    leaf_nonmaximal_exceptional_summand_decay
  refine ⟨min c₁ c₂, max C₁ C₂, min θ₁ θ₂, lt_min hc₁ hc₂,
    lt_of_lt_of_le hC₁ (le_max_left _ _), lt_min hθ₁ hθ₂,
    (min_le_left _ _).trans hθ₁2, fun θ hθ hθle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hmaximal θ hθ (hθle.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hnonmaximal θ hθ (hθle.trans (min_le_right _ _))
  refine ⟨max (max N₁ N₂) 2, fun N hN q χ γ hp hq hz hlo hlt => ?_⟩
  have hN1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hs : (0 : ℝ) ≤ Real.sqrt N / Real.log N :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N from (by omega : 1 ≤ 2).trans ((le_max_right _ _).trans hN))))
  have absorb {E c C : ℝ} (hc : min c₁ c₂ ≤ c) (hC : C ≤ max C₁ C₂)
      (hE : E ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N)) :
      E ≤ max C₁ C₂ * Real.exp (-min c₁ c₂ / θ) * (Real.sqrt N / Real.log N) := by
    apply hE.trans
    apply mul_le_mul_of_nonneg_right _ hs
    apply mul_le_mul hC _ (Real.exp_pos _).le
      (lt_of_lt_of_le hC₁ (le_max_left _ _)).le
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hc) hθ.le)
  by_cases hmax : ∀ γ' : ℝ, χ.LFunction (γ' : ℂ) = 0 →
      1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ' → γ' < 1 → γ' ≤ γ
  · exact absorb (min_le_left _ _) (le_max_left _ _) (hN₁ N hN1 q χ γ hp hq hz hlo hlt hmax)
  · push Not at hmax
    exact absorb (min_le_right _ _) (le_max_right _ _) (hN₂ N hN2 q χ γ hp hq hz hlo hlt hmax)


/-- LEAF. Every pair other than the exceptional one decays together. For a character `x` of
the exceptional family at height `T` equal to `N` to the theta raised to the fifth, of
conductor `x.1 + 1` at most `N` to the theta, and a real zero `γ` of its L function in the
strip below one, the sum over the remaining conductors below the floor of `N` to the theta
together with the primitive characters of conductor `x.1 + 1` other than `x.2` is at most
`C e^{-c/θ} sqrt N / log N`. None of these pairs has its principal term removed, so the
zero gap left by the exceptional family at height `P ^ 5` supplies the saving. -/
theorem leaf_nonexceptional_sum_decay :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
          (∑ k ∈ (range ⌊(N : ℝ) ^ θ⌋₊).erase x.1,
              ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
                Real.pi / (2 * gallagherLength N θ) *
                  Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                    ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                      (gallagherLength N θ) m‖ ^ 2))
            + (∑ χ ∈ ((univ : Finset (DirichletCharacter ℂ (x.1 + 1))).filter
                  (fun χ => χ.IsPrimitive)).erase x.2,
                Real.pi / (2 * gallagherLength N θ) *
                  Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                    ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                      (gallagherLength N θ) m‖ ^ 2))
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  obtain ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, hmean⟩ :=
    LeanLab.Linnik.ExplicitFormula.mean_decay_exceptional_max
  refine ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, fun θ hθ hθle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hmean θ hθ hθle
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₁ N₂, ?_⟩
  rintro N hN ⟨q, ψ⟩ hx hxP γ _hz hγlo _hγ1
  have hP2 : (2 : ℝ) ≤ (N : ℝ) ^ θ := hN₂ N ((le_max_right _ _).trans hN)
  have hT : (2 : ℝ) ≤ ((N : ℝ) ^ θ) ^ 5 :=
    hP2.trans (le_self_pow₀ (by linarith) (by norm_num))
  obtain ⟨γ', hz', hlo', hlt', hmax⟩ :=
    LeanLab.Linnik.ExplicitFormula.exists_max_real_zero hT ⟨q, ψ⟩ hx
  have htotal := hN₁ N ((le_max_left _ _).trans hN) ⟨q, ψ⟩ hx hxP γ' hz' hlo' hlt' hmax
  change (∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        Real.pi / (2 * gallagherLength N θ) *
          Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
            ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ') (N + 1)
              (gallagherLength N θ) m‖ ^ 2)) ≤ _ at htotal
  have hqK : q < ⌊(N : ℝ) ^ θ⌋₊ := by
    have h : q + 1 ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
      (Nat.le_floor_iff (show (0 : ℝ) ≤ (N : ℝ) ^ θ by positivity)).mpr hxP
    omega
  rw [leaf_sum_split_exceptional (N := N) (θ := θ) (γ := γ') ⟨q, ψ⟩ hqK hx.2.1] at htotal
  have heq {k : ℕ} (χ : DirichletCharacter ℂ (k + 1)) (hp : χ.IsPrimitive)
      (hne : (⟨k, χ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ≠ ⟨q, ψ⟩) :
      correctedCoefficient χ (q + 1) γ = correctedCoefficient χ (q + 1) γ' := by
    rw [correctedCoefficient_eq_unexceptional hT ⟨q, ψ⟩ hx k χ hp hne γ hγlo,
      correctedCoefficient_eq_unexceptional hT ⟨q, ψ⟩ hx k χ hp hne γ' hlo']
  have hfirst : (∑ k ∈ (range ⌊(N : ℝ) ^ θ⌋₊).erase q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        Real.pi / (2 * gallagherLength N θ) *
          Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
            ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ) (N + 1)
              (gallagherLength N θ) m‖ ^ 2)) =
      (∑ k ∈ (range ⌊(N : ℝ) ^ θ⌋₊).erase q,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        Real.pi / (2 * gallagherLength N θ) *
          Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
            ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ') (N + 1)
              (gallagherLength N θ) m‖ ^ 2)) := by
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro χ hχ
    rw [heq χ (mem_filter.mp hχ).2 (fun he => (ne_of_mem_erase hk) (congrArg Sigma.fst he))]
  have hsecond : (∑ χ ∈ ((univ : Finset (DirichletCharacter ℂ (q + 1))).filter
        (fun χ => χ.IsPrimitive)).erase ψ,
      Real.pi / (2 * gallagherLength N θ) *
        Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
          ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ) (N + 1)
            (gallagherLength N θ) m‖ ^ 2)) =
      (∑ χ ∈ ((univ : Finset (DirichletCharacter ℂ (q + 1))).filter
        (fun χ => χ.IsPrimitive)).erase ψ,
      Real.pi / (2 * gallagherLength N θ) *
        Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
          ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ') (N + 1)
            (gallagherLength N θ) m‖ ^ 2)) := by
    apply sum_congr rfl
    intro χ hχ
    rw [heq χ (mem_filter.mp (mem_of_mem_erase hχ)).2
      (fun he => (ne_of_mem_erase hχ) (eq_of_heq (Sigma.mk.inj_iff.mp he).2))]
  dsimp only at htotal ⊢
  rw [hfirst, hsecond]
  exact (le_add_of_nonneg_right (by positivity)).trans htotal


/-- LEAF. Two exponential envelopes add to one, at the smaller rate. For positive constants
and positive theta, the sum of the two envelopes of rates `c₁` and `c₂` is at most the sum
of the constants times the single envelope of rate `min c₁ c₂`. -/
theorem leaf_envelope_add {c₁ c₂ C₁ C₂ θ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hθ : 0 < θ) :
    C₁ * Real.exp (-c₁ / θ) + C₂ * Real.exp (-c₂ / θ)
      ≤ (C₁ + C₂) * Real.exp (-(min c₁ c₂) / θ) := by
  have h1 : Real.exp (-c₁ / θ) ≤ Real.exp (-(min c₁ c₂) / θ) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg (min_le_left c₁ c₂)) hθ.le
  have h2 : Real.exp (-c₂ / θ) ≤ Real.exp (-(min c₁ c₂) / θ) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg (min_le_right c₁ c₂)) hθ.le
  rw [add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 hC₁.le)
    (mul_le_mul_of_nonneg_left h2 hC₂.le)

/-- Gallagher 1975 p.131 display 14 and the paragraph following it. The sealed statement:
some positive rate, constant and exponent bound give, for every character of the exceptional
family at height `N` to the theta raised to the fifth and conductor at most `N` to the
theta, a real zero of its L function in the strip below one at which the normalized
corrected energy at that conductor decays as `C e^{-c/θ}`. -/
theorem energy_decay_with_exception_split :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∃ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 ∧
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1 ∧
            normalizedEnergy N θ (x.1 + 1) γ ≤ C * Real.exp (-c / θ) := by
  obtain ⟨c₁, C₁, θ₁, hc₁, hC₁, hθ₁, hθ₁2, hA⟩ := leaf_exceptional_summand_decay
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hθ₂2, hB⟩ := leaf_nonexceptional_sum_decay
  refine ⟨min c₁ c₂, C₁ + C₂, min θ₁ θ₂, lt_min hc₁ hc₂, add_pos hC₁ hC₂,
    lt_min hθ₁ hθ₂, (min_le_left _ _).trans (hθ₁2.trans (by norm_num)),
    fun θ hθ hθle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hA θ hθ (hθle.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hB θ hθ (hθle.trans (min_le_right _ _))
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max N₁ N₂) (max N₃ 4), fun N hN x hx hxP => ?_⟩
  have hN1 : N₁ ≤ N :=
    (le_max_left N₁ N₂).trans ((le_max_left (max N₁ N₂) (max N₃ 4)).trans hN)
  have hN2 : N₂ ≤ N :=
    (le_max_right N₁ N₂).trans ((le_max_left (max N₁ N₂) (max N₃ 4)).trans hN)
  have hN3 : N₃ ≤ N :=
    (le_max_left N₃ 4).trans ((le_max_right (max N₁ N₂) (max N₃ 4)).trans hN)
  have hN4 : 4 ≤ N :=
    (le_max_right N₃ 4).trans ((le_max_right (max N₁ N₂) (max N₃ 4)).trans hN)
  have hP2 : (2 : ℝ) ≤ (N : ℝ) ^ θ := hN₃ N hN3
  have hT : (2 : ℝ) ≤ ((N : ℝ) ^ θ) ^ 5 :=
    hP2.trans (le_self_pow₀ (by linarith) (by norm_num))
  obtain ⟨γ, hz, hlo, hlt⟩ := exceptional_real_zero hT x hx
  obtain ⟨hL, hR⟩ := gallagherLength_spec hθ.le (hθle.trans ((min_le_right _ _).trans hθ₂2)) hN4
  have hqP : (x.1 : ℝ) + 1 ≤ (N : ℝ) ^ θ := by
    have h := hxP
    push_cast at h
    exact h
  have hqK : x.1 < ⌊(N : ℝ) ^ θ⌋₊ := by
    have h : x.1 + 1 ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
      (Nat.le_floor_iff (show (0 : ℝ) ≤ (N : ℝ) ^ θ by positivity)).mpr hxP
    omega
  have hprim : x.2.IsPrimitive := hx.2.1
  have hsumA := hN₁ N hN1 x.1 x.2 γ hprim hqP hz hlo hlt
  have hsumB := hN₂ N hN2 x hx hxP γ hz hlo hlt
  refine ⟨γ, hz, hlo, hlt, ?_⟩
  rw [normalizedEnergy_le_iff (by omega)]
  unfold correctedEnergy
  refine le_trans (sum_le_sum fun k _ => sum_le_sum fun χ _ =>
    energy_window_gallagher χ N (x.1 + 1) _ θ γ hL hR) ?_
  rw [leaf_sum_split_exceptional (N := N) (θ := θ) (γ := γ) x hqK hprim]
  refine le_trans (add_le_add hsumB hsumA) ?_
  have hsq : (0 : ℝ) ≤ Real.sqrt N / Real.log N :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  have heq : C₂ * Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N) +
      C₁ * Real.exp (-c₁ / θ) * (Real.sqrt N / Real.log N)
      = (C₁ * Real.exp (-c₁ / θ) + C₂ * Real.exp (-c₂ / θ)) *
        (Real.sqrt N / Real.log N) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (leaf_envelope_add hC₁ hC₂ hθ) hsq

end LeanLab.Linnik.Decomp486c

#print axioms LeanLab.Linnik.Decomp486c.energy_decay_with_exception_split
