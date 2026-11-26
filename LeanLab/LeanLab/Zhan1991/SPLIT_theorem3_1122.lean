import LeanLab.Zhan1991.Theorems235

/-!
P0068 Zhan 1991, the proof of Theorem 3, page 269, read from the rendered page image of
papers/Zhan1991.pdf, burst-20261122. The proof heading on page 269 is misprinted as
"Proof of Theorem 2"; it is the proof of Theorem 3.

Route: Lemma 6 of reference [2], Pan and Pan, reduces Theorem 3 to the zero density display
(3.19). Display (3.19) splits at beta = 5/6: the low range uses (2.3) of Lemma 4, the high range
uses (2.4) of Lemma 4 and the zero free region of Lemma 5.

The assembly `theorem3_of_split` is PROVED from the two Props `PanPanLemma6` and `Display319`.
`display319_of_ranges` is PROVED from the two range Props. Both range steps below are PROVED,
CONDITIONAL ON their named density and zero free inputs. The four cited inputs remain LEAFs.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open Real

/-- Page 262, Lemma 4: `N(α, T, H, q)`, the number of zeros of `∏_{χ mod q} L(s, χ)` with
`Re s ≥ α` and `T ≤ Im s ≤ T + H`, counted with multiplicity as the sum over the characters
of the analytic orders. Mathlib's `analyticOrderNatAt` is `0` off the zero set and at the pole
of the principal character, so neither adds to the count. -/
def zeroCountZ (α T H : ℝ) (q : ℕ) [NeZero q] : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
        ρ.im ≤ T + H},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)

/-- Page 269, the height `T = q^{1/2} (N A⁻¹ + |λ| N) L^{c₇}` in Lemma 6 of [2]. -/
def T269 (N : ℕ) (A lam : ℝ) (q : ℕ) (c7 : ℝ) : ℝ :=
  Real.sqrt q * ((N : ℝ) / A + |lam| * N) * Real.log N ^ c7

/-- Page 269, the window length `H = 10 (N A⁻¹ + |λ| A)` in Lemma 6 of [2]. -/
def H269 (N : ℕ) (A lam : ℝ) : ℝ :=
  10 * ((N : ℝ) / A + |lam| * A)

/-- Page 262, display (2.3) of Lemma 4, Zhan [4]: for `H ≥ T^{1/3}` and `1/2 ≤ α ≤ 1`,
`N(α, T, H, q) ≪ (qH)^{8/3 (1-α)} (log qH)^{216}`. READING: `T` real, `H ≥ 2` and
`H ≥ |T|^{1/3}`; negative heights are the conjugate characters, see the notes. -/
def Lemma4Eq23 : Prop :=
  ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (α T H : ℝ), 2 ≤ H → |T| ^ (1 / 3 : ℝ) ≤ H →
    1 / 2 ≤ α → α ≤ 1 →
    zeroCountZ α T H q ≤ K * ((q : ℝ) * H) ^ (8 / 3 * (1 - α)) * Real.log (q * H) ^ (216 : ℝ)

/-- Page 262, display (2.4) of Lemma 4: there is an absolute `c₀ > 0` with
`N(α, T, H, q) ≪ (qH)^{12/5 (1-α)} (log qH)^{c₀}` for `H ≥ T^{1/3}` and `5/6 ≤ α ≤ 1`.
Same READING of `T` and `H` as `Lemma4Eq23`. -/
def Lemma4Eq24 : Prop :=
  ∃ c0 : ℝ, 0 < c0 ∧ ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (α T H : ℝ), 2 ≤ H →
    |T| ^ (1 / 3 : ℝ) ≤ H → 5 / 6 ≤ α → α ≤ 1 →
    zeroCountZ α T H q ≤ K * ((q : ℝ) * H) ^ (12 / 5 * (1 - α)) * Real.log (q * H) ^ c0

/-- Page 262, Lemma 5, reference [9], in the form used on page 269: `∏_χ L(s, χ)` has no zero
with `σ ≥ 1 - c₀ / (log q + (log (T + 2))^{4/5})` and `|t| ≤ T`, and for `q ≤ (log T)^c` there
is no exceptional zero. `c₀` is absolute; the threshold `T₀` may depend on `c`. The pole
`s = 1` of the principal character is excluded. -/
def Lemma5NoExc : Prop :=
  ∃ c0 : ℝ, 0 < c0 ∧ ∀ c : ℝ, 0 < c → ∃ T₀ : ℝ, ∀ (q : ℕ) [NeZero q] (T : ℝ), T₀ ≤ T →
    (q : ℝ) ≤ Real.log T ^ c → ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), ρ ≠ 1 →
    DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≤ T →
    ρ.re < 1 - c0 / (Real.log q + Real.log (T + 2) ^ (4 / 5 : ℝ))

/-- Page 269, Lemma 6 of reference [2], Pan and Pan, as it is applied in the proof of
Theorem 3: `S(α; N, A) ≪ L (N H⁻¹ A q⁻¹)^{1/2} max_{1/2 ≤ β ≤ 1} N^{β-1} N(β, T₁, H, q)
+ A L^{-B}` with `|T₁| ≤ 2T`. The maximum is encoded by any bound `M` valid for every `β` and
every admissible `T₁`. The hypotheses are those of Theorem 3 at the point of use; `c₇` is
chosen before `c₃`. -/
def PanPanLemma6 : Prop :=
  ∀ c1 c2 B : ℝ, 0 < c1 → 0 < c2 → 0 < B → ∃ c7 : ℝ, 0 < c7 ∧ ∀ c3 : ℝ, 0 < c3 →
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) [NeZero q], N₀ ≤ N →
      (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam →
      (q : ℝ) ≤ Real.log N ^ c2 →
      Real.log N ^ (B + 1) / A ≤ |lam| →
      ∀ M : ℝ, (∀ β T1 : ℝ, 1 / 2 ≤ β → β ≤ 1 → |T1| ≤ 2 * T269 N A lam q c7 →
          (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ M) →
      ‖Sexp α N A‖ ≤ K * (Real.log N * Real.sqrt ((N : ℝ) / H269 N A lam * A / q) * M +
        A * Real.log N ^ (-B))

/-- The zero density bound (3.19) on `[lo, hi]` for `β`, page 269, with the `T` and `H` of
Lemma 6: `N^{β-1} N(β, T₁, H, q) ≪ L^{-B-1}` once `c₃` is large. -/
def Display319On (lo hi : ℝ) : Prop :=
  ∀ c1 c2 B c7 : ℝ, 0 < c1 → 0 < c2 → 0 < B → 0 < c7 → ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) [NeZero q], N₀ ≤ N →
      (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam →
      (q : ℝ) ≤ Real.log N ^ c2 →
      Real.log N ^ (B + 1) / A ≤ |lam| →
      ∀ β T1 : ℝ, lo ≤ β → β ≤ hi → |T1| ≤ 2 * T269 N A lam q c7 →
        (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ K * Real.log N ^ (-B - 1)

/-- Page 269, display (3.19) for the whole range `1/2 ≤ β ≤ 1`. -/
def Display319 : Prop := Display319On (1 / 2) 1

/-- LEAF: Page 262, Lemma 4, display (2.3), cited from Zhan [4]. HARD, cited input. -/
theorem lemma4_eq23_cited : Lemma4Eq23 := by
  sorry

/-- LEAF: Page 262, Lemma 4, display (2.4), cited from the proof of (2.3) in Zhan [4].
HARD, cited input. -/
theorem lemma4_eq24_cited : Lemma4Eq24 := by
  sorry

/-- LEAF: Page 262, Lemma 5, zero free region of reference [9] with no exceptional zero for
`q ≤ (log T)^c`, Siegel. HARD, cited input. -/
theorem lemma5_cited : Lemma5NoExc := by
  sorry

/-- LEAF: Page 269, the first display of the proof of Theorem 3, Lemma 6 of reference [2].
HARD, cited input. -/
theorem panpan_lemma6_cited : PanPanLemma6 := by
  sorry

/- The existing range proofs import this file. The supporting arguments below are adapted
from ZeroWindowFinite1122, SPLIT_theorem3_p2_1122, SPLIT_display319_high_1122 and
HighDensity1122 here, so these sealed range statements do not acquire a circular import. -/
namespace Task2842

open Filter Topology

/-- Page 262, Lemma 4: zeros of a Dirichlet L function are locally isolated, including near
the principal character's pole. -/
theorem lfun_isolated (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) :
    ∀ᶠ w in 𝓝 z, w ≠ z → DirichletCharacter.LFunction χ w ≠ 0 := by
  set f := DirichletCharacter.LFunction χ
  refine eventually_nhdsWithin_iff.mp ?_
  by_cases hz : z = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := hz
    have hr := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
    have hne : ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp h
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (p : ℂ)⁻¹ = 1 := by linear_combination -h
      have : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) this
      have : (p : ℝ) = 1 := by exact_mod_cast this
      linarith
    filter_upwards [hr.eventually_ne hne] with w hw
    intro h0
    exact hw (mul_eq_zero.mpr (Or.inr h0))
  · have hdiff : DifferentiableOn ℂ f {1}ᶜ := fun w hw =>
      (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
    have hanU : AnalyticOnNhd ℂ f {1}ᶜ := hdiff.analyticOnNhd isOpen_compl_singleton
    have hanz : AnalyticAt ℂ f z := by
      by_cases h1 : z = 1
      · exact (DirichletCharacter.differentiable_LFunction
          (fun h => hz ⟨h1, h⟩)).analyticAt z
      · exact hanU z h1
    rcases hanz.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
        (isConnected_compl_singleton_of_one_lt_rank
          (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
      have hz' : ∃ w : ℂ, w ≠ 1 ∧ f =ᶠ[𝓝 w] 0 := by
        by_cases h1 : z = 1
        · have hev : ∀ᶠ w in 𝓝 z, ∀ᶠ y in 𝓝 w, f y = 0 := h.eventually_nhds
          have hne : ∀ᶠ w in 𝓝[≠] z, w ≠ 1 := by
            subst h1
            exact self_mem_nhdsWithin
          obtain ⟨w, hw1, hw2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and hne).exists
          exact ⟨w, hw2, hw1⟩
        · exact ⟨z, h1, h⟩
      obtain ⟨w, hw1, hw⟩ := hz'
      have hEq := hanU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hw1 hw
      have h2 : f 2 = 0 := hEq (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
        (by norm_num) h2
    · exact h

/-- Page 262, Lemma 4: the zero window is finite by compactness and isolated zeros. -/
theorem zeroWindow_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α T H : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H}.Finite := by
  set f := DirichletCharacter.LFunction χ
  set S := {ρ : ℂ | f ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}
  set K := Complex.equivRealProdCLM.symm '' (Set.Icc α 1 ×ˢ Set.Icc T (T + H))
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hSK : S ⊆ K := by
    intro ρ hρ
    refine ⟨(ρ.re, ρ.im), ⟨⟨hρ.2.1, ?_⟩, hρ.2.2.1, hρ.2.2.2⟩, ?_⟩
    · by_contra hlt
      push Not at hlt
      have hne : ρ ≠ 1 := by
        intro h
        rw [h] at hlt
        simp at hlt
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne) hlt.le hρ.1
    · rfl
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover
    (fun z => {w | w ≠ z → f w ≠ 0}) (fun z _ => lfun_isolated q χ z)
  refine t.finite_toSet.subset ?_
  intro ρ hρ
  obtain ⟨z, hzt, hz⟩ := Set.mem_iUnion₂.mp (hcover (hSK hρ))
  by_contra hnot
  have : ρ ≠ z := fun h => hnot (h ▸ hzt)
  exact hz this hρ.1

/-- Page 269, display 3.19: enlarging the height window increases the zero count. -/
theorem zeroCountZ_mono_H (q : ℕ) [NeZero q] (α T H H' : ℝ) (hH : H ≤ H') :
    zeroCountZ α T H q ≤ zeroCountZ α T H' q := by
  unfold zeroCountZ
  apply Finset.sum_le_sum
  intro χ _
  set s := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
    ρ.im ≤ T + H}
  set s' := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
    ρ.im ≤ T + H'}
  have hss : s ⊆ s' := by
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans (by linarith)⟩
  have hfin : s'.Finite := zeroWindow_finite q χ α T H'
  set g := fun ρ : ℂ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ => Nat.cast_nonneg _
  rw [finsum_mem_def, finsum_mem_def]
  apply finsum_le_finsum
  · exact (hfin.subset hss).subset Set.support_indicator_subset
  · exact hfin.subset Set.support_indicator_subset
  · intro ρ
    exact Set.indicator_le_indicator_of_subset hss hg0 ρ

/-- Page 269: a zero free window has zero count, since the pole has analytic order zero. -/
theorem zeroCountZ_eq_zero_of_free (q : ℕ) [NeZero q] (α T H : ℝ)
    (hfree : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), ρ ≠ 1 →
      DirichletCharacter.LFunction χ ρ = 0 → α ≤ ρ.re → T ≤ ρ.im → ρ.im ≤ T + H → False) :
    zeroCountZ α T H q = 0 := by
  have hone (χ : DirichletCharacter ℂ q) :
      analyticOrderNatAt (DirichletCharacter.LFunction χ) 1 = 0 := by
    by_cases hχ : χ = 1
    · subst hχ
      apply analyticOrderNatAt_of_not_analyticAt
      intro han
      have hc := han.continuousAt
      have h0 : Tendsto (fun s : ℂ =>
          (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
          (𝓝[≠] 1) (𝓝 0) := by
        have h : Tendsto (fun s : ℂ =>
            (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
            (𝓝 1) (𝓝 ((1 - 1) *
              DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) 1)) :=
          ((continuous_id.sub continuous_const).continuousAt.tendsto).mul hc.tendsto
        simpa using h.mono_left nhdsWithin_le_nhds
      have heq := tendsto_nhds_unique
        (DirichletCharacter.LFunctionTrivChar_residue_one (N := q)) h0
      have hne : ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro p hp h
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have : (p : ℂ)⁻¹ = 1 := by linear_combination -h
        have : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) this
        have : (p : ℝ) = 1 := by exact_mod_cast this
        linarith
      exact hne heq
    · unfold analyticOrderNatAt
      rw [analyticOrderAt_eq_zero.mpr
        (Or.inr (DirichletCharacter.LFunction_apply_one_ne_zero hχ))]
      rfl
  unfold zeroCountZ
  apply Finset.sum_eq_zero
  intro χ _
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro ρ hρ
  by_cases h1 : ρ = 1
  · subst h1
    simp [hone χ]
  · exact (hfree χ ρ h1 hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2).elim

/-- Page 269: the rational approximation bounds the perturbation by `N L^c₁ / q A²`. -/
theorem lam_bound269 (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 : ℝ) (hL : 1 ≤ Real.log N)
    (hA0 : 0 < A) (hN : (1 : ℝ) ≤ N) (hq : 1 ≤ q)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    |lam| ≤ N * Real.log N ^ c1 / (q * A ^ 2) := by
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < N := by linarith
  have e : 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1))) =
      N * Real.log N ^ c1 / (q * A ^ 2) := by
    rw [Real.rpow_neg hL0.le]
    have : 0 < Real.log N ^ c1 := Real.rpow_pos_of_pos hL0 _
    field_simp
  rwa [e] at hlam

/-- Page 269: `10 ≤ H ≤ 20 N L^c₁ / A`. -/
theorem H269_bounds (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 : ℝ) (hc1 : 0 ≤ c1)
    (hL : 1 ≤ Real.log N) (hA0 : 0 < A) (hAN : A ≤ N) (hq : 1 ≤ q)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    10 ≤ H269 N A lam ∧ H269 N A lam ≤ 20 * N * Real.log N ^ c1 / A := by
  have hN : (1 : ℝ) ≤ N := by
    by_contra h
    push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hl := lam_bound269 N A lam q c1 hL hA0 hN hq hlam
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP : 1 ≤ Real.log N ^ c1 := Real.one_le_rpow hL hc1
  have hNA : 1 ≤ (N : ℝ) / A := by rw [le_div_iff₀ hA0]; linarith
  have hlA : |lam| * A ≤ N * Real.log N ^ c1 / A := by
    calc |lam| * A ≤ N * Real.log N ^ c1 / (q * A ^ 2) * A :=
          mul_le_mul_of_nonneg_right hl hA0.le
      _ = N * Real.log N ^ c1 / A / q := by field_simp
      _ ≤ N * Real.log N ^ c1 / A := div_le_self (by positivity) hq0
  have hNA2 : (N : ℝ) / A ≤ N * Real.log N ^ c1 / A := by
    rw [mul_div_right_comm]
    exact le_mul_of_one_le_right (by positivity) hP
  unfold H269
  constructor
  · nlinarith [mul_nonneg (abs_nonneg lam) hA0.le]
  · have : 20 * (N : ℝ) * Real.log N ^ c1 / A =
        10 * (N * Real.log N ^ c1 / A + N * Real.log N ^ c1 / A) := by ring
    rw [this]
    linarith

/-- Page 269: `T ≤ 2 q^{1/2} N² L^{c₁+c₇} / A²`. -/
theorem T269_bound (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 c7 : ℝ) (hc1 : 0 ≤ c1)
    (hL : 1 ≤ Real.log N) (hA0 : 0 < A) (hAN : A ≤ N) (hq : 1 ≤ q)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    T269 N A lam q c7 ≤
      2 * Real.sqrt q * ((N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2) * Real.log N ^ c7 := by
  have hN : (1 : ℝ) ≤ N := by
    by_contra h
    push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hl := lam_bound269 N A lam q c1 hL hA0 hN hq hlam
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP : 1 ≤ Real.log N ^ c1 := Real.one_le_rpow hL hc1
  have hL0 : 0 ≤ Real.log N := by linarith
  set R := (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2
  have h1 : (N : ℝ) / A ≤ R := by
    have : (N : ℝ) / A = N * A / A ^ 2 := by field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc (N : ℝ) * A ≤ N * N := mul_le_mul_of_nonneg_left hAN (by linarith)
      _ = N ^ 2 * 1 := by ring
      _ ≤ N ^ 2 * Real.log N ^ c1 := mul_le_mul_of_nonneg_left hP (by positivity)
  have h2 : |lam| * N ≤ R := by
    calc |lam| * N ≤ N * Real.log N ^ c1 / (q * A ^ 2) * N :=
          mul_le_mul_of_nonneg_right hl (by linarith)
      _ = R / q := by simp only [R]; field_simp
      _ ≤ R := div_le_self (by positivity) hq0
  unfold T269
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hc : 0 ≤ Real.log N ^ c7 := Real.rpow_nonneg hL0 _
  calc Real.sqrt q * ((N : ℝ) / A + |lam| * N) * Real.log N ^ c7
      ≤ Real.sqrt q * (R + R) * Real.log N ^ c7 := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- Page 269: with `x = N^{1/8}`, the working windows satisfy `T ≤ 2x⁶` and `H ≤ 20x³`. -/
theorem window_x_bounds269 (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 c2 c3 c7 : ℝ) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hc7 : 0 ≤ c7) (hc3 : c1 + c2 + c7 ≤ c3) (hN : (4096 : ℝ) ≤ N)
    (hL : 1 ≤ Real.log N) (hA : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A) (hAN : A ≤ N)
    (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ Real.log N ^ c2)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    T269 N A lam q c7 ≤ 2 * ((N : ℝ) ^ (1 / 8 : ℝ)) ^ 6 ∧
      H269 N A lam ≤ 20 * ((N : ℝ) ^ (1 / 8 : ℝ)) ^ 3 := by
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set x := (N : ℝ) ^ (1 / 8 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0 _
  have hx8 : x ^ 8 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have hP : (N : ℝ) ^ (5 / 8 : ℝ) = x ^ 5 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have hx5pos : 0 < x ^ 5 := by
    have : 0 < x := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hLc3 : 1 ≤ L ^ c3 := Real.one_le_rpow hL (by linarith)
  have hA0 : 0 < A := by nlinarith [hP ▸ hA]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsq : Real.sqrt q ≤ L ^ c2 := by
    refine le_trans ?_ hqL
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  obtain ⟨_, hH⟩ := H269_bounds N A lam q c1 hc1 hL hA0 hAN hq hlam
  have hT := T269_bound N A lam q c1 c7 hc1 hL hA0 hAN hq hlam
  have hA2 : x ^ 10 * L ^ (c1 + c2 + c7) ≤ A ^ 2 := by
    have h1 : L ^ (c1 + c2 + c7) ≤ L ^ c3 := Real.rpow_le_rpow_of_exponent_le hL hc3
    have h2 : x ^ 5 * L ^ (c1 + c2 + c7) ≤ A := by
      rw [← hP]
      exact (mul_le_mul_of_nonneg_left h1 (by rw [hP]; exact hx5pos.le)).trans hA
    have h3 : x ^ 5 ≤ x ^ 5 * L ^ (c1 + c2 + c7) :=
      le_mul_of_one_le_right hx5pos.le (Real.one_le_rpow hL (by linarith))
    calc x ^ 10 * L ^ (c1 + c2 + c7) =
          x ^ 5 * (x ^ 5 * L ^ (c1 + c2 + c7)) := by ring
      _ ≤ A * A := mul_le_mul (h3.trans h2) h2 (by positivity) hA0.le
      _ = A ^ 2 := by ring
  have hTb : T269 N A lam q c7 ≤ 2 * x ^ 6 := by
    have hLsum : L ^ c2 * L ^ c1 * L ^ c7 = L ^ (c1 + c2 + c7) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0]
      ring
    have hpos : 0 < L ^ (c1 + c2 + c7) := Real.rpow_pos_of_pos hL0 _
    calc T269 N A lam q c7 ≤
          2 * Real.sqrt q * ((N : ℝ) ^ 2 * L ^ c1 / A ^ 2) * L ^ c7 := hT
      _ ≤ 2 * L ^ c2 * ((N : ℝ) ^ 2 * L ^ c1 / A ^ 2) * L ^ c7 := by gcongr
      _ = 2 * (N : ℝ) ^ 2 * (L ^ c2 * L ^ c1 * L ^ c7) / A ^ 2 := by ring
      _ = 2 * x ^ 16 * L ^ (c1 + c2 + c7) / A ^ 2 := by rw [hLsum, ← hx8]; ring
      _ ≤ 2 * x ^ 16 * L ^ (c1 + c2 + c7) /
          (x ^ 10 * L ^ (c1 + c2 + c7)) := by gcongr
      _ = 2 * x ^ 6 := by
          have : x ^ 10 ≠ 0 := by positivity
          field_simp
  have hHb : H269 N A lam ≤ 20 * x ^ 3 := by
    have h1 : L ^ c1 ≤ L ^ c3 := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have hLc1 : 0 < L ^ c1 := Real.rpow_pos_of_pos hL0 _
    have h2 : x ^ 5 * L ^ c1 ≤ A := by
      rw [← hP]
      exact (mul_le_mul_of_nonneg_left h1 (by rw [hP]; exact hx5pos.le)).trans hA
    calc H269 N A lam ≤ 20 * N * L ^ c1 / A := hH
      _ ≤ 20 * N * L ^ c1 / (x ^ 5 * L ^ c1) := by gcongr
      _ = 20 * x ^ 3 := by rw [← hx8]; field_simp
  exact ⟨hTb, hHb⟩

end Task2842

set_option maxHeartbeats 1600000 in
/-- Page 269, the low range of 3.19. PROVED, CONDITIONAL ON 2.3 of Lemma 4.
Enlarge the window by `2 N^{1/4} + 2` to meet `H ≥ |T₁|^{1/3}`. Its cost is absorbed into
`H' ≤ 24 N^{3/8} L^{c₁-c₃}`, retaining the logarithmic saving since `1 - β ≥ 1/6`.
The sealed Lemma 5 argument is unnecessary. -/
theorem display319_low_of_23 (h23 : Lemma4Eq23) (h5 : Lemma5NoExc) :
    Display319On (1 / 2) (5 / 6) := by
  have hgrowth : ∀ δ k : ℝ, 0 < δ → ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
      Real.log 24 ≤ δ * Real.log L ∧ L ^ k ≤ Real.exp (L / 8) ∧ 2 ≤ L := by
    intro δ k hδ
    have h1 : ∀ᶠ L : ℝ in Filter.atTop, Real.log 24 ≤ δ * Real.log L := by
      have h := Real.tendsto_log_atTop.eventually
        (Filter.eventually_ge_atTop (Real.log 24 / δ))
      filter_upwards [h] with L hL
      rw [div_le_iff₀ hδ] at hL
      linarith
    have h2 : ∀ᶠ L : ℝ in Filter.atTop, L ^ k ≤ Real.exp (L / 8) := by
      have h := (isLittleO_rpow_exp_pos_mul_atTop k
        (by norm_num : (0 : ℝ) < 1 / 8)).bound (by norm_num : (0 : ℝ) < 1)
      filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with L hL hL0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0 _),
        abs_of_nonneg (Real.exp_pos _).le, one_mul] at hL
      calc L ^ k ≤ Real.exp (1 / 8 * L) := hL
        _ = _ := by congr 1; ring
    exact Filter.eventually_atTop.mp
      (h1.and (h2.and (Filter.eventually_ge_atTop (2 : ℝ))))
  obtain ⟨K23, h23'⟩ := h23
  intro c1 c2 B c7 hc1 hc2 hB hc7
  set δ : ℝ := 9 * (217 + B) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set c3 : ℝ := c1 + c2 + c7 + 1 + δ with hc3
  obtain ⟨L0, hL0⟩ := hgrowth δ (c3 - c1) hδ0
  refine ⟨c3, by rw [hc3]; linarith, |K23| * 24 ^ (4 / 9 : ℝ),
    max (max 4096 (Real.exp L0)) (Real.exp 1), ?_⟩
  intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN4 : (4096 : ℝ) ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNL0 : L0 ≤ Real.log N := by
    have := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    simpa using Real.log_le_log (Real.exp_pos L0) this
  obtain ⟨hasA, hasB, hasC⟩ := hL0 (Real.log N) hNL0
  have hq1 : 1 ≤ q := hcond.2.2.2.1
  obtain ⟨hTx, -⟩ := Task2842.window_x_bounds269 N A lam q c1 c2 c3 c7 hc1.le hc2.le
    hc7.le (by rw [hc3]; linarith) hN4 hL1 hA hAN hq1 hq hcond.2.2.1
  have hN0 : (0 : ℝ) < N := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hN0 _)
      (Real.rpow_pos_of_pos (by linarith) _)) hA
  obtain ⟨h10, hH⟩ := Task2842.H269_bounds N A lam q c1 hc1.le hL1 hA0 hAN hq1 hcond.2.2.1
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  set x := (N : ℝ) ^ (1 / 8 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  have hx8 : x ^ 8 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hP : (N : ℝ) ^ (5 / 8 : ℝ) = x ^ 5 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hx1 : 1 ≤ x := by
    by_contra h
    push Not at h
    have : x ^ 8 < 1 := pow_lt_one₀ hx0 h (by norm_num)
    linarith
  have hxpos : 0 < x := by linarith
  have hlogx : Real.log x = L / 8 := by
    rw [hx, Real.log_rpow hN0]
    ring
  have hxexp : x = Real.exp (L / 8) := by
    rw [← hlogx, Real.exp_log hxpos]
  clear_value x L
  have hLc : 0 < L ^ (c1 - c3) := Real.rpow_pos_of_pos hLpos _
  have hHs : H269 N A lam ≤ 20 * x ^ 3 * L ^ (c1 - c3) := by
    have h1 : x ^ 5 * L ^ c3 ≤ A := by rw [← hP]; exact hA
    have hc3p : 0 < L ^ c3 := Real.rpow_pos_of_pos hLpos _
    have e : L ^ (c1 - c3) = L ^ c1 / L ^ c3 := Real.rpow_sub hLpos _ _
    calc H269 N A lam ≤ 20 * N * L ^ c1 / A := hH
      _ ≤ 20 * N * L ^ c1 / (x ^ 5 * L ^ c3) := by
          have : 0 < x ^ 5 * L ^ c3 := by positivity
          gcongr
      _ = 20 * x ^ 3 * L ^ (c1 - c3) := by
          rw [e, ← hx8]
          field_simp
  have hx2 : 2 * x ^ 2 + 2 ≤ 4 * x ^ 3 * L ^ (c1 - c3) := by
    have hk : L ^ (c3 - c1) ≤ x := by rw [hxexp]; exact hasB
    have hinv : L ^ (c1 - c3) * L ^ (c3 - c1) = 1 := by
      rw [← Real.rpow_add hLpos]
      simp
    have hx2' : 1 ≤ x ^ 2 := one_le_pow₀ hx1
    have : x ^ 2 ≤ x ^ 3 * L ^ (c1 - c3) := by
      have := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ x ^ 2 * L ^ (c1 - c3))
      calc x ^ 2 = x ^ 2 * (L ^ (c1 - c3) * L ^ (c3 - c1)) := by rw [hinv, mul_one]
        _ = x ^ 2 * L ^ (c1 - c3) * L ^ (c3 - c1) := by ring
        _ ≤ x ^ 2 * L ^ (c1 - c3) * x := this
        _ = x ^ 3 * L ^ (c1 - c3) := by ring
    linarith
  set H' := H269 N A lam + 2 * x ^ 2 + 2 with hH'
  clear_value H'
  have hH'0 : 0 ≤ H269 N A lam := by linarith
  have hH'2 : 2 ≤ H' := by rw [hH']; nlinarith
  have hT1' : |T1| ^ (1 / 3 : ℝ) ≤ H' := by
    have h1 : |T1| ≤ (2 * x ^ 2) ^ 3 := by nlinarith
    have h2 := Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have h3 : ((2 * x ^ 2) ^ 3) ^ (1 / 3 : ℝ) = 2 * x ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h3] at h2
    rw [hH']
    linarith
  have hmono := Task2842.zeroCountZ_mono_H q β T1 (H269 N A lam) H' (by rw [hH']; nlinarith)
  have hz := h23' q β T1 H' hH'2 hT1' hβ0 (by linarith)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hLc2 : 0 < L ^ c2 := Real.rpow_pos_of_pos hLpos _
  have hH'x : H' ≤ 24 * x ^ 3 * L ^ (c1 - c3) := by rw [hH']; linarith
  have hqH0 : 0 < (q : ℝ) * H' := by positivity
  have hlogqH : Real.log ((q : ℝ) * H') ≤ Real.log 24 - δ * Real.log L + 3 * (L / 8) := by
    have h1 : (q : ℝ) * H' ≤ L ^ c2 * (24 * x ^ 3 * L ^ (c1 - c3)) :=
      mul_le_mul hq hH'x (by positivity) hLc2.le
    have h2 := Real.log_le_log hqH0 h1
    have h3 : Real.log (L ^ c2 * (24 * x ^ 3 * L ^ (c1 - c3))) =
        Real.log 24 - (c7 + 1 + δ) * Real.log L + 3 * (L / 8) := by
      rw [Real.log_mul hLc2.ne' (by positivity), Real.log_rpow hLpos,
        Real.log_mul (by positivity) hLc.ne', Real.log_rpow hLpos,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogx, hc3]
      push_cast
      ring
    have : 0 ≤ (c7 + 1) * Real.log L := mul_nonneg (by linarith) (Real.log_nonneg hL1)
    linarith
  have hlogqH0 : 0 ≤ Real.log ((q : ℝ) * H') :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1' (by linarith))
  have hlogqHL : Real.log ((q : ℝ) * H') ≤ L := by
    have : 0 ≤ δ * Real.log L := mul_nonneg hδ0.le (Real.log_nonneg hL1)
    linarith
  have hsave : (N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) ≤
      Real.exp (4 / 9 * (Real.log 24 - δ * Real.log L)) := by
    have hu : 1 / 6 ≤ 1 - β := by linarith
    have hneg : Real.log 24 - δ * Real.log L ≤ 0 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hlogqH (by positivity : (0 : ℝ) ≤ 8 / 3 * (1 - β))
    have h2 := mul_le_mul_of_nonpos_right hu hneg
    have key : L * (β - 1) + Real.log ((q : ℝ) * H') * (8 / 3 * (1 - β)) ≤
        4 / 9 * (Real.log 24 - δ * Real.log L) := by
      linear_combination h1 + 8 / 3 * h2
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hqH0, ← Real.exp_add, ← hLdef]
    exact Real.exp_le_exp.mpr key
  have hexpval : Real.exp (4 / 9 * (Real.log 24 - δ * Real.log L)) =
      24 ^ (4 / 9 : ℝ) * L ^ (-(217 + B)) := by
    rw [show 4 / 9 * (Real.log 24 - δ * Real.log L) =
        Real.log 24 * (4 / 9) + Real.log L * (-(217 + B)) by rw [hδ]; ring,
      Real.exp_add, ← Real.rpow_def_of_pos (by norm_num), ← Real.rpow_def_of_pos hLpos]
  have hlogpow : Real.log ((q : ℝ) * H') ^ (216 : ℝ) ≤ L ^ (216 : ℝ) :=
    Real.rpow_le_rpow hlogqH0 hlogqHL (by norm_num)
  have hNb : 0 ≤ (N : ℝ) ^ (β - 1) := Real.rpow_nonneg hN0.le _
  have hpow : L ^ (-(217 + B)) * L ^ (216 : ℝ) = L ^ (-B - 1) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  have h24p : 0 ≤ (24 : ℝ) ^ (4 / 9 : ℝ) := by positivity
  calc (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q
      ≤ (N : ℝ) ^ (β - 1) * (K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) *
          Real.log ((q : ℝ) * H') ^ (216 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmono.trans hz) hNb
    _ ≤ (N : ℝ) ^ (β - 1) * (|K23| * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) *
          Real.log ((q : ℝ) * H') ^ (216 : ℝ)) := by
        have := Real.rpow_nonneg hqH0.le (8 / 3 * (1 - β))
        have := Real.rpow_nonneg hlogqH0 (216 : ℝ)
        gcongr
        exact le_abs_self _
    _ = |K23| * (((N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β))) *
          Real.log ((q : ℝ) * H') ^ (216 : ℝ)) := by ring
    _ ≤ |K23| * ((24 ^ (4 / 9 : ℝ) * L ^ (-(217 + B))) * L ^ (216 : ℝ)) := by
        rw [← hexpval]
        have := Real.rpow_nonneg hlogqH0 (216 : ℝ)
        gcongr
    _ = |K23| * 24 ^ (4 / 9 : ℝ) * L ^ (-B - 1) := by rw [← hpow]; ring

set_option maxHeartbeats 1600000 in
/-- Page 269, the high range of 3.19. PROVED, CONDITIONAL ON 2.4 of Lemma 4 and Lemma 5.
Apply Lemma 5 at height `N`, where `q ≤ L^{c₂} = (log N)^{c₂}`: the count is zero for
`β ≥ 1 - c₀/(log q + (log (N + 2))^{4/5})`, so `1 - β ≫ L^{-4/5}` on the remaining range. -/
theorem display319_high_of_24 (h24 : Lemma4Eq24) (h5 : Lemma5NoExc) :
    Display319On (5 / 6) 1 := by
  obtain ⟨c0', hc0', K24, h24'⟩ := h24
  obtain ⟨c0, hc0, h5'⟩ := h5
  intro c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨T₀, hT₀⟩ := h5' c2 hc2
  have ha : ∀ᶠ L : ℝ in Filter.atTop, Real.log L ≤ 1 / (96 * c2) * L := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound
      (by positivity : (0 : ℝ) < 1 / (96 * c2))
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with L hL hL1
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_nonneg (by linarith)] at hL
    exact hL
  have hb : ∀ᶠ L : ℝ in Filter.atTop, Real.log L ≤ 1 / c2 * L ^ (4 / 5 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).bound
      (by positivity : (0 : ℝ) < 1 / c2)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with L hL hL1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hL
    exact hL
  have hc : ∀ᶠ L : ℝ in Filter.atTop,
      L ^ (B + 1 + c0') ≤ Real.exp (c0 * L ^ (1 / 5 : ℝ) / 60) := by
    have hy : ∀ᶠ y : ℝ in Filter.atTop,
        y ^ (5 * (B + 1 + c0')) ≤ Real.exp (c0 / 60 * y) := by
      have h := (isLittleO_rpow_exp_pos_mul_atTop (5 * (B + 1 + c0'))
        (by positivity : 0 < c0 / 60)).bound (by norm_num : (0 : ℝ) < 1)
      filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with y hy hy0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy0 _),
        abs_of_nonneg (Real.exp_pos _).le, one_mul] at hy
      exact hy
    have ht : Filter.Tendsto (fun L : ℝ => L ^ (1 / 5 : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    filter_upwards [ht.eventually hy, Filter.eventually_ge_atTop (0 : ℝ)] with L hL hL0
    have e : (L ^ (1 / 5 : ℝ)) ^ (5 * (B + 1 + c0')) = L ^ (B + 1 + c0') := by
      rw [← Real.rpow_mul hL0]
      congr 1
      ring
    rw [e] at hL
    calc L ^ (B + 1 + c0') ≤ Real.exp (c0 / 60 * L ^ (1 / 5 : ℝ)) := hL
      _ = _ := by congr 1; ring
  have hd : ∀ᶠ L : ℝ in Filter.atTop, Real.log 24 ≤ L / 96 := by
    filter_upwards [Filter.eventually_ge_atTop (96 * Real.log 24)] with L hL
    linarith
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.mp (ha.and (hb.and (hc.and hd)))
  refine ⟨c1 + c2 + c7 + 1, by linarith, |K24|,
    max (max T₀ 4096) (max (Real.exp L0) (Real.exp 1)), ?_⟩
  intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
  have he : Real.exp 1 ≤ (N : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN4 : (4096 : ℝ) ≤ N :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNT : T₀ ≤ (N : ℝ) :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNL0 : L0 ≤ Real.log N := by
    have := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    simpa using Real.log_le_log (Real.exp_pos L0) this
  obtain ⟨hg1, hg2, hasC, hg4⟩ := hL0 (Real.log N) hNL0
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hasA : Real.log 24 + c2 * Real.log L ≤ L / 48 := by
    have h := mul_le_mul_of_nonneg_left hg1 hc2.le
    have e : c2 * (1 / (96 * c2) * L) = L / 96 := by field_simp
    rw [e] at h
    linarith
  have hasB : c2 * Real.log L ≤ L ^ (4 / 5 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hg2 hc2.le
    have e : c2 * (1 / c2 * L ^ (4 / 5 : ℝ)) = L ^ (4 / 5 : ℝ) := by field_simp
    rwa [e] at h
  have hq1 : 1 ≤ q := hcond.2.2.2.1
  obtain ⟨hTx, hHx⟩ := Task2842.window_x_bounds269 N A lam q c1 c2
    (c1 + c2 + c7 + 1) c7 hc1.le hc2.le hc7.le (by linarith)
    hN4 hL1 hA hAN hq1 hq hcond.2.2.1
  have hN0 : (0 : ℝ) < N := by linarith
  set x := (N : ℝ) ^ (1 / 8 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  have hx8 : x ^ 8 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hx2 : 8 ≤ x ^ 2 := by
    by_contra h
    push Not at h
    have : (x ^ 2) ^ 4 < 8 ^ 4 :=
      pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have : x ^ 8 < 4096 := by nlinarith
    linarith
  have hx1 : 1 ≤ x := by nlinarith
  have hxpos : 0 < x := by linarith
  have hlogx : Real.log x = L / 8 := by
    rw [hx, Real.log_rpow hN0]
    ring
  clear_value x L
  have hwin : 2 * T269 N A lam q c7 + H269 N A lam ≤ N := by
    have hx3 : 5 ≤ x ^ 3 := by nlinarith
    have : 4 * x ^ 6 + 20 * x ^ 3 ≤ x ^ 8 := by
      nlinarith [mul_le_mul_of_nonneg_right hx2 (pow_nonneg hx0 6),
        mul_le_mul_of_nonneg_right hx3 (pow_nonneg hx0 3)]
    linarith
  by_cases hfree : 1 - c0 / (Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ)) ≤ β
  · have hz : zeroCountZ β T1 (H269 N A lam) q = 0 := by
      apply Task2842.zeroCountZ_eq_zero_of_free
      intro χ ρ hρ1 hρ0 hre him1 him2
      have habs : |ρ.im| ≤ N := by
        rw [abs_le]
        have := abs_le.mp hT1
        constructor <;> nlinarith [abs_nonneg T1, le_abs_self T1, neg_abs_le T1]
      have := hT₀ q N hNT (by simpa only [← hLdef] using hq) χ ρ hρ1 hρ0 habs
      linarith
    rw [hz, mul_zero]
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hLpos.le _)
  · push Not at hfree
    set H' := 20 * x ^ 3 + 2 * x ^ 2 + 2 with hH'
    clear_value H'
    have hHH' : H269 N A lam ≤ H' := by nlinarith
    have hH'2 : 2 ≤ H' := by nlinarith
    have hT1' : |T1| ^ (1 / 3 : ℝ) ≤ H' := by
      have h1 : |T1| ≤ (2 * x ^ 2) ^ 3 := by nlinarith
      have h2 := Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have h3 : ((2 * x ^ 2) ^ 3) ^ (1 / 3 : ℝ) = 2 * x ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [h3] at h2
      nlinarith
    have hmono := Task2842.zeroCountZ_mono_H q β T1 (H269 N A lam) H' hHH'
    have hz := h24' q β T1 H' hH'2 hT1' hβ0 hβ1
    have hD0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
    have hlogN2 : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith)
    have hDpos : 0 < Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) :=
      add_pos_of_nonneg_of_pos hD0 (Real.rpow_pos_of_pos hlogN2 _)
    have hu0 : c0 / (Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ)) < 1 - β := by
      linarith
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hLc2 : 0 < L ^ c2 := Real.rpow_pos_of_pos hLpos _
    have hH'x : H' ≤ 24 * x ^ 3 := by
      have h1 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      have h2 : 1 ≤ x ^ 3 := one_le_pow₀ hx1
      rw [hH']
      linarith
    have hqH0 : 0 < (q : ℝ) * H' := by positivity
    have hlogqH : Real.log ((q : ℝ) * H') ≤ 19 * L / 48 := by
      have h1 : (q : ℝ) * H' ≤ L ^ c2 * (24 * x ^ 3) :=
        mul_le_mul hq hH'x (by positivity) hLc2.le
      have h2 := Real.log_le_log hqH0 h1
      have h3 : Real.log (L ^ c2 * (24 * x ^ 3)) =
          c2 * Real.log L + Real.log 24 + 3 * (L / 8) := by
        rw [Real.log_mul hLc2.ne' (by positivity), Real.log_rpow hLpos,
          Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogx]
        push_cast
        ring
      linarith
    have hlogqH0 : 0 ≤ Real.log ((q : ℝ) * H') :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1' (by linarith))
    have hsave : (N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) ≤
        Real.exp (-((1 - β) * L / 20)) := by
      have hu : 0 ≤ 1 - β := by linarith
      have h := mul_le_mul_of_nonneg_left hlogqH
        (by positivity : (0 : ℝ) ≤ 12 / 5 * (1 - β))
      have key : L * (β - 1) + Real.log ((q : ℝ) * H') * (12 / 5 * (1 - β)) ≤
          -((1 - β) * L / 20) := by linear_combination h
      rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hqH0, ← Real.exp_add, ← hLdef]
      exact Real.exp_le_exp.mpr key
    have hDle : Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) ≤
        3 * L ^ (4 / 5 : ℝ) := by
      have h1 : Real.log q ≤ c2 * Real.log L := by
        have := Real.log_le_log (by linarith) hq
        rwa [Real.log_rpow hLpos] at this
      have h2 : Real.log ((N : ℝ) + 2) ≤ 2 * L := by
        have : (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by nlinarith
        have := Real.log_le_log (by linarith) this
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have h3 : Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) ≤ (2 * L) ^ (4 / 5 : ℝ) :=
        Real.rpow_le_rpow hlogN2.le h2 (by norm_num)
      have h4 : (2 * L) ^ (4 / 5 : ℝ) ≤ 2 * L ^ (4 / 5 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hLpos.le]
        have h : (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        rw [Real.rpow_one] at h
        exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hLpos.le _)
      linarith
    have hL45 : 0 < L ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hLpos _
    have hsplitL : L = L ^ (4 / 5 : ℝ) * L ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_add hLpos]
      norm_num
    have hexp : c0 * L ^ (1 / 5 : ℝ) / 60 ≤ (1 - β) * L / 20 := by
      have h1 : c0 / (3 * L ^ (4 / 5 : ℝ)) ≤ 1 - β :=
        (div_le_div_of_nonneg_left hc0.le hDpos hDle).trans hu0.le
      rw [div_le_iff₀ (by positivity)] at h1
      have hL15 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLpos.le _
      calc c0 * L ^ (1 / 5 : ℝ) / 60 ≤
            (1 - β) * (3 * L ^ (4 / 5 : ℝ)) * L ^ (1 / 5 : ℝ) / 60 := by gcongr
        _ = (1 - β) * (L ^ (4 / 5 : ℝ) * L ^ (1 / 5 : ℝ)) / 20 := by ring
        _ = (1 - β) * L / 20 := by rw [← hsplitL]
    have hsave2 : (N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) ≤
        Real.exp (-(c0 * L ^ (1 / 5 : ℝ) / 60)) :=
      hsave.trans (Real.exp_le_exp.mpr (by linarith))
    have hlogpow : Real.log ((q : ℝ) * H') ^ c0' ≤ L ^ c0' :=
      Real.rpow_le_rpow hlogqH0 (by linarith) hc0'.le
    have hNb : 0 ≤ (N : ℝ) ^ (β - 1) := Real.rpow_nonneg hN0.le _
    have hfinal : Real.exp (-(c0 * L ^ (1 / 5 : ℝ) / 60)) * L ^ c0' ≤
        L ^ (-B - 1) := by
      have hE := Real.exp_pos (c0 * L ^ (1 / 5 : ℝ) / 60)
      rw [Real.exp_neg]
      have hsum : L ^ (B + 1 + c0') = L ^ (B + 1) * L ^ c0' := by
        rw [Real.rpow_add hLpos]
      have hinv : L ^ (-B - 1) = (L ^ (B + 1))⁻¹ := by
        rw [show (-B - 1 : ℝ) = -(B + 1) by ring, Real.rpow_neg hLpos.le]
      rw [hinv, inv_mul_eq_div, le_inv_comm₀ (by positivity) (by positivity), inv_div,
        le_div_iff₀ (by positivity)]
      calc L ^ (B + 1) * L ^ c0' = L ^ (B + 1 + c0') := hsum.symm
        _ ≤ _ := hasC
        _ = _ := by ring
    have hS0 : 0 ≤ ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) := Real.rpow_nonneg hqH0.le _
    have hlog0 : 0 ≤ Real.log ((q : ℝ) * H') ^ c0' := Real.rpow_nonneg hlogqH0 _
    calc (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q
        ≤ (N : ℝ) ^ (β - 1) * (K24 * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) *
            Real.log ((q : ℝ) * H') ^ c0') :=
          mul_le_mul_of_nonneg_left (hmono.trans hz) hNb
      _ ≤ (N : ℝ) ^ (β - 1) * (|K24| * ((q : ℝ) * H') ^ (12 / 5 * (1 - β)) *
            Real.log ((q : ℝ) * H') ^ c0') := by
          gcongr
          exact le_abs_self _
      _ = |K24| * (((N : ℝ) ^ (β - 1) * ((q : ℝ) * H') ^ (12 / 5 * (1 - β))) *
            Real.log ((q : ℝ) * H') ^ c0') := by ring
      _ ≤ |K24| * (Real.exp (-(c0 * L ^ (1 / 5 : ℝ) / 60)) * L ^ c0') := by gcongr
      _ ≤ |K24| * L ^ (-B - 1) := by gcongr

/-- Page 269, combining the two ranges of (3.19) at `β = 5/6`. PROVED. -/
theorem display319_of_ranges (hlo : Display319On (1 / 2) (5 / 6))
    (hhi : Display319On (5 / 6) 1) : Display319 := by
  intro c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨d1, hd1, K1, N1, h1⟩ := hlo c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨d2, hd2, K2, N2, h2⟩ := hhi c1 c2 B c7 hc1 hc2 hB hc7
  refine ⟨max d1 d2, lt_of_lt_of_le hd1 (le_max_left _ _), max K1 K2,
    max (max N1 N2) (Real.exp 1), ?_⟩
  intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp (by norm_num)).trans he
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hL0 : 0 ≤ Real.log N := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hP : 0 ≤ Real.log N ^ (-B - 1) := Real.rpow_nonneg hL0 _
  have hAd : ∀ d, d ≤ max d1 d2 → (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ d ≤ A := by
    intro d hd
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hd)
      (Real.rpow_nonneg hN0 _)).trans hA
  rcases le_total β (5 / 6) with hβ | hβ
  · have := h1 N A α lam a q ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
      (hAd d1 (le_max_left _ _)) hAN hcond hq hlam β T1 hβ0 hβ hT1
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hP)
  · have := h2 N A α lam a q ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
      (hAd d2 (le_max_right _ _)) hAN hcond hq hlam β T1 hβ hβ1 hT1
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP)

/-- The factor in Lemma 6 is at most `A`: `H ≥ 10 N A⁻¹` gives `N H⁻¹ A q⁻¹ ≤ A²`. Page 269,
the step from Lemma 6 to the first sufficient condition. PROVED. -/
theorem sqrt_factor_le269 (N : ℕ) (A lam : ℝ) (q : ℕ) (hq : 1 ≤ q) (hA : 0 ≤ A) :
    Real.sqrt ((N : ℝ) / H269 N A lam * A / q) ≤ A := by
  rw [Real.sqrt_le_left hA]
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rcases hA.eq_or_lt with h0 | hpos
  · subst h0; simp
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hH : 10 * ((N : ℝ) / A) ≤ H269 N A lam := by
    unfold H269
    have : 0 ≤ |lam| * A := mul_nonneg (abs_nonneg _) hpos.le
    linarith
  rcases hN0.eq_or_lt with hN | hN
  · rw [← hN]; simp; positivity
  have hNA : 0 < (N : ℝ) / A := div_pos hN hpos
  have hHpos : 0 < H269 N A lam := by linarith
  have h1 : (N : ℝ) / H269 N A lam ≤ A / 10 := by
    rw [div_le_iff₀ hHpos]
    have : (N : ℝ) = A / 10 * (10 * ((N : ℝ) / A)) := by field_simp
    calc (N : ℝ) = A / 10 * (10 * ((N : ℝ) / A)) := this
      _ ≤ A / 10 * H269 N A lam := mul_le_mul_of_nonneg_left hH (by positivity)
  have h2 : (N : ℝ) / H269 N A lam * A / q ≤ A / 10 * A := by
    rw [div_le_iff₀ (by linarith)]
    have h3 : (N : ℝ) / H269 N A lam * A ≤ A / 10 * A := mul_le_mul_of_nonneg_right h1 hpos.le
    have h4 : 0 ≤ A / 10 * A := by positivity
    nlinarith
  nlinarith

/-- Page 269, the proof of Theorem 3: Lemma 6 of [2] and display (3.19) give Theorem 3.
PROVED, CONDITIONAL on the two named Props. -/
theorem theorem3_of_split (h6 : PanPanLemma6) (h319 : Display319) : Theorem3 := by
  intro c1 c2 B hc1 hc2 hB
  obtain ⟨c7, hc7, h6'⟩ := h6 c1 c2 B hc1 hc2 hB
  obtain ⟨c3, hc3, K9, N9, h9⟩ := h319 c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨K6, N6, h6c⟩ := h6' c3 hc3
  refine ⟨c3, hc3, |K6| * (|K9| + 1), max (max N6 N9) 3, ?_⟩
  intro N A α lam a q hN hA hAN hcond hq hlam
  have hq1 : 1 ≤ q := hcond.2.2.2.1
  have : NeZero q := ⟨by omega⟩
  have h3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA0 : 0 ≤ A :=
    (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hLpos.le _)).trans hA
  set L := Real.log N with hLdef
  set M := |K9| * L ^ (-B - 1) with hM
  have hMb : ∀ β T1 : ℝ, 1 / 2 ≤ β → β ≤ 1 → |T1| ≤ 2 * T269 N A lam q c7 →
      (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ M := by
    intro β T1 hb0 hb1 hT
    exact (h9 N A α lam a q ((le_max_right _ _).trans ((le_max_left _ _).trans hN)) hA hAN
      hcond hq hlam β T1 hb0 hb1 hT).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hLpos.le _))
  have hS := h6c N A α lam a q ((le_max_left _ _).trans ((le_max_left _ _).trans hN)) hA hAN
    hcond hq hlam M hMb
  have hsq := sqrt_factor_le269 N A lam q hq1 hA0
  have hLB : L * L ^ (-B - 1) = L ^ (-B) := by
    rw [show (-B - 1 : ℝ) = -B - 1 by ring, Real.rpow_sub hLpos, Real.rpow_one]
    field_simp
  have hX0 : 0 ≤ L * Real.sqrt ((N : ℝ) / H269 N A lam * A / q) * M + A * L ^ (-B) := by
    have : 0 ≤ M := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hLpos.le _)
    have := Real.sqrt_nonneg ((N : ℝ) / H269 N A lam * A / q)
    have := Real.rpow_nonneg hLpos.le (-B)
    positivity
  have hX : L * Real.sqrt ((N : ℝ) / H269 N A lam * A / q) * M + A * L ^ (-B) ≤
      (|K9| + 1) * A * L ^ (-B) := by
    have hM0 : 0 ≤ M := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hLpos.le _)
    have h1 : L * Real.sqrt ((N : ℝ) / H269 N A lam * A / q) * M ≤ L * A * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hLpos.le) hM0
    have h2 : L * A * M = |K9| * A * L ^ (-B) := by
      rw [hM, ← hLB]; ring
    nlinarith
  calc ‖Sexp α N A‖ ≤ K6 * (L * Real.sqrt ((N : ℝ) / H269 N A lam * A / q) * M +
        A * L ^ (-B)) := hS
    _ ≤ |K6| * (L * Real.sqrt ((N : ℝ) / H269 N A lam * A / q) * M + A * L ^ (-B)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hX0
    _ ≤ |K6| * ((|K9| + 1) * A * L ^ (-B)) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
    _ = |K6| * (|K9| + 1) * A * L ^ (-B) := by ring

/-- Theorem 3 of page 260 from the split: the cited Lemma 6 of [2], the cited Lemmas 4 and 5,
and the two range steps of (3.19). PROVED from LEAFs; its axioms show `sorryAx` until the
LEAFs are closed. -/
theorem zhan_theorem3_split : Theorem3 :=
  theorem3_of_split panpan_lemma6_cited
    (display319_of_ranges (display319_low_of_23 lemma4_eq23_cited lemma5_cited)
      (display319_high_of_24 lemma4_eq24_cited lemma5_cited))

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.display319_low_of_23
#print axioms LeanLab.Zhan1991.display319_high_of_24
