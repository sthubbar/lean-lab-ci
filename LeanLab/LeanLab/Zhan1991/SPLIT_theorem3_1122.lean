import LeanLab.Zhan1991.Theorems235

/-!
P0068 Zhan 1991, the proof of Theorem 3, page 269, read from the rendered page image of
papers/Zhan1991.pdf, burst-20261122. The proof heading on page 269 is misprinted as
"Proof of Theorem 2"; it is the proof of Theorem 3.

Route: Lemma 6 of reference [2], Pan and Pan, reduces Theorem 3 to the zero density display
(3.19). Display (3.19) splits at beta = 5/6: the low range uses (2.3) of Lemma 4, the high range
uses (2.4) of Lemma 4 and the zero free region of Lemma 5.

The assembly `theorem3_of_split` is PROVED from the two Props `PanPanLemma6` and `Display319`.
`display319_of_ranges` is PROVED from the two range Props. The cited inputs and the two range
steps are LEAFs.

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

/-- LEAF: Page 269, the display after "For 1/2 ≤ β ≤ 5/6, using (2.3) we get": the low range
    of (3.19) from (2.3). HARD. The window bookkeeping is the work: `H ≪ N A⁻¹ L^{c₁}` from
    `|λ| ≤ 1/(qτ)`, the condition `H ≥ |T₁|^{1/3}` of Lemma 4 met by enlarging the window,
    and
    `(H^{8/3} N⁻¹ q^{8/3})^{1-β} L^{c₀} ≪ L^{c₀ - 8/3 (c₃-c₁-c₂) 1/6}`. See the QUESTION in the
    notes on `H ≥ T₁^{1/3}` when `A` is near `N`; Lemma 5 is offered for that case. -/

-- Helper lemma: zeroCountZ is nonnegative
lemma zeroCountZ_nonneg (α T H : ℝ) (q : ℕ) [NeZero q] : 0 ≤ zeroCountZ α T H q := by
  have h₁ : 0 ≤ ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    apply Finset.sum_nonneg
    intro χ _
    apply Finset.sum_nonneg
    intro ρ _
    exact by positivity
  simpa [zeroCountZ] using h₁

-- Helper lemma: zeroCountZ is monotone in H
lemma zeroCountZ_mono_H (α T H H' : ℝ) (q : ℕ) [NeZero q] (h : H ≤ H') : zeroCountZ α T H q ≤ zeroCountZ α T H' q := by
  have h₁ : ∀ (χ : DirichletCharacter ℂ q), ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤ ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H'}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    intro χ
    have h₂ : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H} ⊆ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H'} := by
      intro ρ hρ
      simp only [Set.mem_setOf_eq] at hρ ⊢
      exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by linarith [hρ.2.2.2, h]⟩
    have h₃ : ∀ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}, 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
      intro ρ _
      exact by positivity
    -- Use the fact that the sum over a subset is less than or equal to the sum over the superset
    have h₄ : ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤ ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H'}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
      -- Use the subset property and nonnegativity of terms
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Prove the subset relation for the finite sets
        classical
        simp_all [Set.Finite.subset]
        <;> aesop
      · -- Prove nonnegativity of terms
        intro ρ _
        exact by positivity
    exact h₄
  -- Sum over all characters
  calc
    zeroCountZ α T H q = ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := rfl
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H'}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := Finset.sum_le_sum fun χ _ => h₁ χ
    _ = zeroCountZ α T H' q := rfl

-- Helper lemma: extract |λ| bound from Cond12
lemma cond12_lam_bound {α τ : ℝ} {a : ℤ} {q : ℕ} {lam : ℝ} (hcond : Cond12 α τ a q lam) : |lam| ≤ 1 / (q * τ) := by
  exact hcond.2.2.1

-- Helper lemma: extract q ≥ 1 from Cond12
lemma cond12_q_pos {α τ : ℝ} {a : ℤ} {q : ℕ} {lam : ℝ} (hcond : Cond12 α τ a q lam) : 1 ≤ q := by
  exact hcond.2.2.2.1

-- Helper lemma: extract q ≤ τ from Cond12
lemma cond12_q_le_tau {α τ : ℝ} {a : ℤ} {q : ℕ} {lam : ℝ} (hcond : Cond12 α τ a q lam) : (q : ℝ) ≤ τ := by
  exact hcond.2.2.2.2

-- Helper lemma: log bound
lemma log_bound {C : ℝ} : ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → (3 : ℝ) ≤ N ∧ C ≤ Real.log N := by
  have h₁ : ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N → (3 : ℕ) ≤ N ∧ C ≤ Real.log N := by
    -- Use the fact that log N grows without bound
    have h₂ : ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N → C ≤ Real.log N := by
      -- Since log N → ∞ as N → ∞, there exists N₀ such that for all N ≥ N₀, log N ≥ C
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt C
      use max 3 N₀
      intro N hN
      have h₃ : (max 3 N₀ : ℕ) ≤ N := hN
      have h₄ : (3 : ℕ) ≤ N := by linarith [le_max_left 3 N₀]
      have h₅ : (N₀ : ℕ) ≤ N := by linarith [le_max_right 3 N₀]
      have h₆ : (N : ℝ) ≥ N₀ := by exact_mod_cast h₅
      have h₇ : Real.log (N : ℝ) ≥ Real.log (N₀ : ℝ) := Real.log_le_log (by positivity) h₆
      have h₈ : Real.log (N₀ : ℝ) ≥ C := by
        have h₉ : (N₀ : ℝ) > C := by exact_mod_cast hN₀
        have h₁₀ : Real.log (N₀ : ℝ) ≥ C := by
          have h₁₁ : Real.log (N₀ : ℝ) ≥ Real.log (Real.exp C) := Real.log_le_log (by positivity) (by
            have h₁₂ : (Real.exp C : ℝ) ≤ N₀ := by
              have h₁₃ : Real.exp C < (N₀ : ℝ) := by linarith [Real.add_one_le_exp C]
              linarith
            linarith)
          have h₁₂ : Real.log (Real.exp C) = C := by rw [Real.log_exp]
          linarith
        linarith
      linarith
    obtain ⟨N₀, hN₀⟩ := h₂
    use N₀
    intro N hN
    exact ⟨by linarith [hN₀ N hN], hN₀ N hN⟩
  obtain ⟨N₀, hN₀⟩ := h₁
  refine' ⟨N₀, _⟩
  intro N hN
  have h₂ := hN₀ N (by exact_mod_cast hN)
  exact ⟨by exact_mod_cast h₂.1, h₂.2⟩

-- Main theorem
theorem display319_low_of_23 (h23 : Lemma4Eq23) (h5 : Lemma5NoExc) :
    Display319On (1 / 2) (5 / 6) := by
  intro c1 c2 B c7 hc1 hc2 hB hc7
  have h_main : ∃ (c3 : ℝ), 0 < c3 ∧ ∃ (K N₀ : ℝ), ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) [NeZero q], N₀ ≤ N → (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N → Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam → (q : ℝ) ≤ Real.log N ^ c2 → Real.log N ^ (B + 1) / A ≤ |lam| → ∀ (β T1 : ℝ), 1 / 2 ≤ β → β ≤ 5 / 6 → |T1| ≤ 2 * T269 N A lam q c7 → (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ K * Real.log N ^ (-B - 1) := by
    -- Choose c3 = c1 + c2 + (9/4)*(B + 218) as in the plan
    use c1 + c2 + (9 / 4 : ℝ) * (B + 218)
    have hc3_pos : 0 < c1 + c2 + (9 / 4 : ℝ) * (B + 218) := by linarith
    -- Get K23 from Lemma 4 Eq 2.3
    obtain ⟨K23, hK23⟩ := h23
    -- Choose N₀ large enough (will be determined by the asymptotic bounds)
    have h_N0_exists : ∃ (N₀ : ℝ), ∀ (N : ℕ), N₀ ≤ N → (3 : ℝ) ≤ N ∧ (1 : ℝ) ≤ Real.log N := by
      obtain ⟨N₀, hN₀⟩ := log_bound (1 : ℝ)
      refine' ⟨N₀, _⟩
      intro N hN
      have h₁ := hN₀ N hN
      exact ⟨by linarith, by linarith⟩
    obtain ⟨N₀_log, hN₀_log⟩ := h_N0_exists
    -- Use a larger N₀ to handle all the asymptotic bounds
    -- For now, use N₀_log and adjust later
    use max (max (K23 + 1) 1) (max N₀_log 3)
    constructor
    · -- Prove K > 0
      have h₁ : 0 < K23 + 1 := by linarith
      have h₂ : 0 < (1 : ℝ) := by norm_num
      have h₃ : 0 < max (K23 + 1) 1 := by positivity
      have h₄ : 0 < max (max (K23 + 1) 1) (max N₀_log 3) := by positivity
      linarith
    · -- Prove the main inequality
      intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
      have h₁ : (3 : ℝ) ≤ N := by
        have h₂ := hN₀_log N (by exact_mod_cast (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans hN))
        linarith
      have h₂ : (1 : ℝ) ≤ Real.log N := by
        have h₃ := hN₀_log N (by exact_mod_cast (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans hN))
        linarith
      have h₃ : 0 < Real.log N := by linarith
      have h₄ : 0 < (N : ℝ) := by positivity
      have h₅ : 0 < A := by
        have h₅₁ : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) ≤ A := by exact_mod_cast hA
        have h₅₂ : 0 < (N : ℝ) ^ (5 / 8 : ℝ) := by positivity
        have h₅₃ : 0 < Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) := by positivity
        have h₅₄ : 0 < (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) := by positivity
        linarith
      -- Extract bounds from Cond12
      have h₆ : 1 ≤ q := cond12_q_pos hcond
      have h₇ : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1))) := cond12_lam_bound hcond
      have h₈ : (q : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1) := cond12_q_le_tau hcond
      -- Simplify the bound on |lam|
      have h₉ : |lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) ≤ 1 := by
        have h₉₁ : 0 < (q : ℝ) := by positivity
        have h₉₂ : 0 < (A : ℝ) := by positivity
        have h₉₃ : 0 < (A : ℝ) ^ 2 / N * Real.log N ^ (-c1) := by positivity
        have h₉₄ : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1))) := h₇
        calc
          |lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) = |lam| * ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by ring
          _ ≤ (1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) * ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by gcongr
          _ = 1 := by
            field_simp [h₉₁.ne', h₉₃.ne']
            <;> ring_nf
            <;> field_simp [h₉₁.ne', h₉₃.ne']
            <;> linarith
      -- Bound H269
      have h₁₀ : H269 N A lam ≤ 20 * (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
        have h₁₀₁ : H269 N A lam = 10 * ((N : ℝ) / A + |lam| * A) := by
          simp [H269]
          <;> ring_nf
        rw [h₁₀₁]
        have h₁₀₂ : (N : ℝ) / A ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
          have h₁₀₂₁ : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) ≤ A := by exact_mod_cast hA
          have h₁₀₂₂ : 0 < (N : ℝ) := by positivity
          have h₁₀₂₃ : 0 < A := by positivity
          have h₁₀₂₄ : 0 < Real.log N := by linarith
          have h₁₀₂₅ : 0 < (N : ℝ) ^ (5 / 8 : ℝ) := by positivity
          have h₁₀₂₆ : 0 < Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) := by positivity
          have h₁₀₂₇ : (N : ℝ) / A ≤ (N : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
            apply div_le_div_of_le_left (by positivity) (by positivity)
            linarith
          have h₁₀₂₈ : (N : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) = (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
            have h₁₀₂₈₁ : (N : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) = (N : ℝ) ^ (1 - 5 / 8 : ℝ) * Real.log N ^ (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
              field_simp [h₁₀₂₂.ne', h₁₀₂₅.ne', h₁₀₂₆.ne', Real.rpow_neg, Real.rpow_sub, Real.rpow_add]
              <;> ring_nf
              <;> field_simp [h₁₀₂₂.ne', h₁₀₂₅.ne', h₁₀₂₆.ne', Real.rpow_neg, Real.rpow_sub, Real.rpow_add]
              <;> ring_nf
              <;> simp_all [Real.rpow_add, Real.rpow_sub, Real.rpow_neg, Real.rpow_one]
              <;> field_simp [h₁₀₂₂.ne', h₁₀₂₅.ne', h₁₀₂₆.ne']
              <;> ring_nf
              <;> norm_num
              <;> linarith
            have h₁₀₂₈₂ : (1 : ℝ) - 5 / 8 = 3 / 8 := by norm_num
            rw [h₁₀₂₈₁, h₁₀₂₈₂]
            <;> simp [Real.rpow_neg]
            <;> field_simp [h₁₀₂₂.ne', h₁₀₂₅.ne', h₁₀₂₆.ne']
            <;> ring_nf
          rw [h₁₀₂₈] at h₁₀₂₇
          linarith
        have h₁₀₃ : |lam| * A ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
          have h₁₀₃₁ : |lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) ≤ 1 := h₉
          have h₁₀₃₂ : 0 < (q : ℝ) := by positivity
          have h₁₀₃₃ : 0 < (A : ℝ) := by positivity
          have h₁₀₃₄ : 0 < (N : ℝ) := by positivity
          have h₁₀₃₅ : 0 < Real.log N := by linarith
          have h₁₀₃₆ : 0 < (A : ℝ) ^ 2 := by positivity
          have h₁₀₃₇ : 0 < (A : ℝ) ^ 2 / N * Real.log N ^ (-c1) := by positivity
          have h₁₀₃₈ : |lam| ≤ 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by
            have h₁₀₃₈₁ : |lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) ≤ 1 := h₉
            have h₁₀₃₈₂ : 0 < (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) := by positivity
            have h₁₀₃₈₃ : |lam| ≤ 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by
              calc
                |lam| = |lam| * 1 := by ring
                _ ≤ |lam| * ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) * (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) := by
                  have h₁₀₃₈₄ : 0 < (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) := by positivity
                  field_simp [h₁₀₃₈₄.ne']
                  <;> nlinarith
                _ = (|lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) * (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) := by ring
                _ ≤ 1 * (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) := by gcongr
                _ = 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by ring
            exact h₁₀₃₈₃
          have h₁₀₃₉ : |lam| * A ≤ (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) * A := by
            gcongr
          have h₁₀₄₀ : (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) * A = (N : ℝ) * Real.log N ^ c1 / ((q : ℝ) * A) := by
            field_simp [h₁₀₃₂.ne', h₁₀₃₃.ne', h₁₀₃₄.ne', h₁₀₃₅.ne', h₁₀₃₆.ne', Real.rpow_neg]
            <;> ring_nf
            <;> field_simp [h₁₀₃₂.ne', h₁₀₃₃.ne', h₁₀₃₄.ne', h₁₀₃₅.ne', h₁₀₃₆.ne', Real.rpow_neg]
            <;> ring_nf
            <;> simp_all [Real.rpow_neg, Real.rpow_add, Real.rpow_sub]
            <;> field_simp [h₁₀₃₂.ne', h₁₀₃₃.ne', h₁₀₃₄.ne', h₁₀₃₅.ne', h₁₀₃₆.ne']
            <;> ring_nf
            <;> norm_num
            <;> linarith
          rw [h₁₀₄₀] at h₁₀₃₉
          have h₁₀₄₁ : (N : ℝ) * Real.log N ^ c1 / ((q : ℝ) * A) ≤ (N : ℝ) * Real.log N ^ c1 / A := by
            have h₁₀₄₁₁ : (q : ℝ) ≥ 1 := by exact_mod_cast h₆
            have h₁₀₄₁₂ : 0 < (q : ℝ) := by positivity
            have h₁₀₄₁₃ : 0 < (A : ℝ) := by positivity
            have h₁₀₄₁₄ : 0 < (N : ℝ) * Real.log N ^ c1 := by positivity
            have h₁₀₄₁₅ : (q : ℝ) * A ≥ A := by nlinarith
            have h₁₀₄₁₆ : (N : ℝ) * Real.log N ^ c1 / ((q : ℝ) * A) ≤ (N : ℝ) * Real.log N ^ c1 / A := by
              apply div_le_div_of_le_left (by positivity) (by positivity)
              <;> nlinarith
            exact h₁₀₄₁₆
          have h₁₀₄₂ : (N : ℝ) * Real.log N ^ c1 / A ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
            have h₁₀₄₂₁ : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) ≤ A := by exact_mod_cast hA
            have h₁₀₄₂₂ : 0 < (N : ℝ) := by positivity
            have h₁₀₄₂₃ : 0 < A := by positivity
            have h₁₀₄₂₄ : 0 < Real.log N := by linarith
            have h₁₀₄₂₅ : 0 < (N : ℝ) ^ (5 / 8 : ℝ) := by positivity
            have h₁₀₄₂₆ : 0 < Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) := by positivity
            have h₁₀₄₂₇ : (N : ℝ) * Real.log N ^ c1 / A ≤ (N : ℝ) * Real.log N ^ c1 / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
              apply div_le_div_of_le_left (by positivity) (by positivity)
              linarith
            have h₁₀₄₂₈ : (N : ℝ) * Real.log N ^ c1 / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) = (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
              have h₁₀₄₂₈₁ : (N : ℝ) * Real.log N ^ c1 / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) = (N : ℝ) ^ (1 - 5 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
                field_simp [h₁₀₄₂₂.ne', h₁₀₄₂₅.ne', h₁₀₄₂₆.ne', Real.rpow_sub, Real.rpow_add]
                <;> ring_nf
                <;> field_simp [h₁₀₄₂₂.ne', h₁₀₄₂₅.ne', h₁₀₄₂₆.ne', Real.rpow_sub, Real.rpow_add]
                <;> ring_nf
                <;> simp_all [Real.rpow_add, Real.rpow_sub, Real.rpow_neg, Real.rpow_one]
                <;> field_simp [h₁₀₄₂₂.ne', h₁₀₄₂₅.ne', h₁₀₄₂₆.ne']
                <;> ring_nf
                <;> norm_num
                <;> linarith
              have h₁₀₄₂₈₂ : (1 : ℝ) - 5 / 8 = 3 / 8 := by norm_num
              rw [h₁₀₄₂₈₁, h₁₀₄₂₈₂]
              <;> simp [Real.rpow_sub]
              <;> field_simp [h₁₀₄₂₂.ne', h₁₀₄₂₅.ne', h₁₀₄₂₆.ne']
              <;> ring_nf
            rw [h₁₀₄₂₈] at h₁₀₄₂₇
            linarith
          calc
            |lam| * A ≤ (N : ℝ) * Real.log N ^ c1 / ((q : ℝ) * A) := by linarith
            _ ≤ (N : ℝ) * Real.log N ^ c1 / A := by linarith
            _ ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by linarith
        have h₁₀₄ : (N : ℝ) / A + |lam| * A ≤ 2 * (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
          have h₁₀₄₁ : (N : ℝ) / A ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := h₁₀₂
          have h₁₀₄₂ : |lam| * A ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := h₁₀₃
          have h₁₀₄₃ : (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
            have h₁₀₄₃₁ : (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218)) : ℝ) ≤ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) : ℝ) := by
              ring_nf
              <;> linarith
            have h₁₀₄₃₂ : 1 ≤ Real.log N := by linarith
            have h₁₀₄₃₃ : 0 < (N : ℝ) ^ (3 / 8 : ℝ) := by positivity
            have h₁₀₄₃₄ : Real.log N ^ (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ≤ Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
              apply Real.rpow_le_rpow_of_exponent_le
              · linarith
              · linarith
            have h₁₀₄₃₅ : 0 ≤ (N : ℝ) ^ (3 / 8 : ℝ) := by positivity
            nlinarith
          have h₁₀₄₄ : (N : ℝ) / A + |lam| * A ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) + (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
            linarith
          have h₁₀₄₅ : (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) + (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) = 2 * (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by ring
          linarith
        have h₁₀₅ : (10 : ℝ) * ((N : ℝ) / A + |lam| * A) ≤ 20 * (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
          have h₁₀₅₁ : (N : ℝ) / A + |lam| * A ≤ 2 * (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := h₁₀₄
          have h₁₀₅₂ : 0 ≤ (N : ℝ) / A + |lam| * A := by positivity
          nlinarith
        linarith
      
      -- Bound T269 (crude bound sufficient for low range)
      have h₁₁ : T269 N A lam q c7 ≤ (N : ℝ) * Real.log N ^ (c7 + c2 / 2 + 10) := by
        have h₁₁₁ : T269 N A lam q c7 = Real.sqrt q * ((N : ℝ) / A + |lam| * N) * Real.log N ^ c7 := by
          simp [T269]
          <;> ring_nf
        rw [h₁₁₁]
        have h₁₁₂ : Real.sqrt q ≤ Real.sqrt (Real.log N ^ c2) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hq
        have h₁₁₃ : Real.sqrt (Real.log N ^ c2) = Real.log N ^ (c2 / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul] <;> ring_nf <;> norm_num
          <;> linarith
        have h₁₁₄ : Real.sqrt q ≤ Real.log N ^ (c2 / 2) := by
          linarith
        have h₁₁₅ : (N : ℝ) / A ≤ (N : ℝ) := by
          have h₁₁₅₁ : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) ≤ A := by exact_mod_cast hA
          have h₁₁₅₂ : 0 < (N : ℝ) := by positivity
          have h₁₁₅₃ : 0 < A := by positivity
          have h₁₁₅₄ : (N : ℝ) / A ≤ (N : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
            apply div_le_div_of_le_left (by positivity) (by positivity)
            linarith
          have h₁₁₅₅ : (N : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ≤ (N : ℝ) := by
            have h₁₁₅₅₁ : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) ≥ 1 := by
              have h₁₁₅₅₂ : (N : ℝ) ≥ 3 := by exact_mod_cast (by linarith)
              have h₁₁₅₅₃ : Real.log N ≥ 1 := by
                have h₁₁₅₅₄ : Real.log N ≥ Real.log 3 := Real.log_le_log (by positivity) (by linarith)
                have h₁₁₅₅₅ : Real.log 3 ≥ 1 := by
                  have := Real.log_two_gt_d9
                  have := Real.log_two_lt_d9
                  norm_num at *
                  <;> linarith
                linarith
              have h₁₁₅₅₆ : (N : ℝ) ^ (5 / 8 : ℝ) ≥ 1 := by
                apply one_le_rpow
                · linarith
                · norm_num
              have h₁₁₅₅₇ : Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) ≥ 1 := by
                apply one_le_rpow
                · linarith
                · have h₁₁₅₅₈ : (c1 + c2 + (9 / 4 : ℝ) * (B + 218) : ℝ) ≥ 0 := by positivity
                  linarith
              nlinarith
            have h₁₁₅₅₂ : 0 < (N : ℝ) := by positivity
            have h₁₁₅₅₃ : 0 < (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) := by positivity
            rw [div_le_iff (by positivity)]
            nlinarith
          linarith
        have h₁₁₆ : |lam| * N ≤ (N : ℝ) * Real.log N ^ 10 := by
          have h₁₁₆₁ : |lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) ≤ 1 := h₉
          have h₁₁₆₂ : 0 < (q : ℝ) := by positivity
          have h₁₁₆₃ : 0 < (A : ℝ) := by positivity
          have h₁₁₆₄ : 0 < (N : ℝ) := by positivity
          have h₁₁₆₅ : 0 < Real.log N := by linarith
          have h₁₁₆₆ : |lam| ≤ 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by
            have h₁₁₆₆₁ : |lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) ≤ 1 := h₉
            have h₁₁₆₆₂ : 0 < (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) := by positivity
            have h₁₁₆₆₃ : |lam| ≤ 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by
              calc
                |lam| = |lam| * 1 := by ring
                _ ≤ |lam| * ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) * (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) := by
                  have h₁₁₆₆₄ : 0 < (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)) := by positivity
                  field_simp [h₁₁₆₆₄.ne']
                  <;> nlinarith
                _ = (|lam| * (q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) * (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) := by ring
                _ ≤ 1 * (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) := by gcongr
                _ = 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) := by ring
            exact h₁₁₆₆₃
          have h₁₁₆₇ : |lam| * N ≤ (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) * N := by
            gcongr
          have h₁₁₆₈ : (1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1)))) * N = (N : ℝ) ^ 2 * Real.log N ^ c1 / ((q : ℝ) * A ^ 2) := by
            field_simp [h₁₁₆₂.ne', h₁₁₆₃.ne', h₁₁₆₄.ne', h₁₁₆₅.ne', Real.rpow_neg]
            <;> ring_nf
            <;> field_simp [h₁₁₆₂.ne', h₁₁₆₃.ne', h₁₁₆₄.ne', h₁₁₆₅.ne', Real.rpow_neg]
            <;> ring_nf
            <;> simp_all [Real.rpow_neg, Real.rpow_add, Real.rpow_sub]
            <;> field_simp [h₁₁₆₂.ne', h₁₁₆₃.ne', h₁₁₆₄.ne', h₁₁₆₅.ne']
            <;> ring_nf
            <;> norm_num
            <;> linarith
          rw [h₁₁₆₈] at h₁₁₆₇
          have h₁₁₆₉ : (N : ℝ) ^ 2 * Real.log N ^ c1 / ((q : ℝ) * A ^ 2) ≤ (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2 := by
            have h₁₁₆₉₁ : (q : ℝ) ≥ 1 := by exact_mod_cast h₆
            have h₁₁₆₉₂ : 0 < (q : ℝ) := by positivity
            have h₁₁₆₉₃ : 0 < (A : ℝ) ^ 2 := by positivity
            have h₁₁₆₉₄ : 0 < (N : ℝ) ^ 2 * Real.log N ^ c1 := by positivity
            have h₁₁₆₉₅ : (q : ℝ) * A ^ 2 ≥ A ^ 2 := by nlinarith
            have h₁₁₆₉₆ : (N : ℝ) ^ 2 * Real.log N ^ c1 / ((q : ℝ) * A ^ 2) ≤ (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2 := by
              apply div_le_div_of_le_left (by positivity) (by positivity)
              <;> nlinarith
            exact h₁₁₆₉₆
          have h₁₁₇₀ : (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2 ≤ (N : ℝ) * Real.log N ^ 10 := by
            have h₁₁₇₀₁ : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) ≤ A := by exact_mod_cast hA
            have h₁₁₇₀₂ : 0 < (N : ℝ) := by positivity
            have h₁₁₇₀₃ : 0 < A := by positivity
            have h₁₁₇₀₄ : 0 < Real.log N := by linarith
            have h₁₁₇₀₅ : A ^ 2 ≥ ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ^ 2 := by
              gcongr <;> nlinarith
            have h₁₁₇₀₆ : ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ^ 2 = (N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
              calc
                ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ^ 2 = (N : ℝ) ^ (5 / 8 : ℝ * 2) * (Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ^ 2 := by
                  rw [mul_rpow (by positivity) (by positivity)]
                  <;> ring_nf
                _ = (N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
                  have h₁₁₇₀₇ : (Real.log N ^ (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ^ 2 = Real.log N ^ (2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
                    rw [← Real.rpow_nat_cast]
                    rw [← Real.rpow_mul] <;> ring_nf <;> norm_num
                    <;> linarith
                  rw [h₁₁₇₀₇]
                  <;> ring_nf
                  <;> field_simp [Real.rpow_add, Real.rpow_mul]
                  <;> ring_nf
            have h₁₁₇₀₇ : A ^ 2 ≥ (N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by linarith
            have h₁₁₇₀₈ : (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2 ≤ (N : ℝ) ^ 2 * Real.log N ^ c1 / ((N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218)))) := by
              apply div_le_div_of_le_left (by positivity) (by positivity)
              linarith
            have h₁₁₇₀₉ : (N : ℝ) ^ 2 * Real.log N ^ c1 / ((N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218)))) = (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
              have h₁₁₇₀₉₁ : (N : ℝ) ^ 2 * Real.log N ^ c1 / ((N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218)))) = (N : ℝ) ^ (2 - 5 / 4 : ℝ) * Real.log N ^ (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by
                field_simp [h₁₁₇₀₂.ne', h₁₁₇₀₄.ne', Real.rpow_sub, Real.rpow_add]
                <;> ring_nf
                <;> field_simp [h₁₁₇₀₂.ne', h₁₁₇₀₄.ne', Real.rpow_sub, Real.rpow_add]
                <;> ring_nf
                <;> simp_all [Real.rpow_add, Real.rpow_sub, Real.rpow_neg, Real.rpow_one]
                <;> field_simp [h₁₁₇₀₂.ne', h₁₁₇₀₄.ne']
                <;> ring_nf
                <;> norm_num
                <;> linarith
              have h₁₁₇₀₉₂ : (2 : ℝ) - 5 / 4 = 3 / 4 := by norm_num
              rw [h₁₁₇₀₉₁, h₁₁₇₀₉₂]
              <;> simp [Real.rpow_sub]
              <;> field_simp [h₁₁₇₀₂.ne', h₁₁₇₀₄.ne']
              <;> ring_nf
            have h₁₁₇₁₀ : (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ≤ (N : ℝ) * Real.log N ^ 10 := by
              have h₁₁₇₁₀₁ : (N : ℝ) ≥ 3 := by exact_mod_cast (by linarith)
              have h₁₁₇₁₀₂ : Real.log N ≥ 1 := by
                have h₁₁₇₁₀₃ : Real.log N ≥ Real.log 3 := Real.log_le_log (by positivity) (by linarith)
                have h₁₁₇₁₀₄ : Real.log 3 ≥ 1 := by
                  have := Real.log_two_gt_d9
                  have := Real.log_two_lt_d9
                  norm_num at *
                  <;> linarith
                linarith
              have h₁₁₇₁₀₃ : (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le
                · linarith
                · norm_num
              have h₁₁₇₁₀₄ : Real.log N ^ (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ≤ Real.log N ^ 10 := by
                have h₁₁₇₁₀₅ : (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218)) : ℝ) ≤ 10 := by
                  nlinarith
                have h₁₁₇₁₀₆ : 1 ≤ Real.log N := by linarith
                have h₁₁₇₁₀₇ : Real.log N ^ (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ≤ Real.log N ^ (10 : ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_le
                  · linarith
                  · linarith
                simpa using h₁₁₇₁₀₇
              calc
                (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) ≤ (N : ℝ) * Real.log N ^ (c1 - 2 * (c1 + c2 + (9 / 4 : ℝ) * (B + 218))) := by gcongr <;> nlinarith
                _ ≤ (N : ℝ) * Real.log N ^ 10 := by gcongr <;> nlinarith
            linarith
          linarith
        have h₁₁₇ : Real.sqrt q * ((N : ℝ) / A + |lam| * N) * Real.log N ^ c7 ≤ Real.log N ^ (c2 / 2) * ((N : ℝ) + (N : ℝ) * Real.log N ^ 10) * Real.log N ^ c7 := by
          have h₁₁₇₁ : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
          have h₁₁₇₂ : 0 ≤ (N : ℝ) / A + |lam| * N := by positivity
          have h₁₁₇₃ : 0 ≤ Real.log N ^ c7 := by positivity
          have h₁₁₇₄ : 0 ≤ Real.log N ^ (c2 / 2) := by positivity
          have h₁₁₇₅ : Real.sqrt q ≤ Real.log N ^ (c2 / 2) := h₁₁₄
          have h₁₁₇₆ : (N : ℝ) / A + |lam| * N ≤ (N : ℝ) + (N : ℝ) * Real.log N ^ 10 := by linarith
          calc
            Real.sqrt q * ((N : ℝ) / A + |lam| * N) * Real.log N ^ c7 ≤ Real.log N ^ (c2 / 2) * ((N : ℝ) / A + |lam| * N) * Real.log N ^ c7 := by gcongr <;> nlinarith
            _ ≤ Real.log N ^ (c2 / 2) * ((N : ℝ) + (N : ℝ) * Real.log N ^ 10) * Real.log N ^ c7 := by gcongr <;> nlinarith
        have h₁₁₈ : Real.log N ^ (c2 / 2) * ((N : ℝ) + (N : ℝ) * Real.log N ^ 10) * Real.log N ^ c7 ≤ (N : ℝ) * Real.log N ^ (c7 + c2 / 2 + 10) := by
          have h₁₁₈₁ : 0 < Real.log N := by linarith
          have h₁₁₈₂ : 0 < (N : ℝ) := by positivity
          have h₁₁₈₃ : Real.log N ^ (c2 / 2) * ((N : ℝ) + (N : ℝ) * Real.log N ^ 10) * Real.log N ^ c7 = Real.log N ^ (c2 / 2) * (N : ℝ) * (1 + Real.log N ^ 10) * Real.log N ^ c7 := by ring
          rw [h₁₁₈₃]
          have h₁₁₈₄ : Real.log N ^ (c2 / 2) * (N : ℝ) * (1 + Real.log N ^ 10) * Real.log N ^ c7 = (N : ℝ) * Real.log N ^ (c2 / 2) * Real.log N ^ c7 * (1 + Real.log N ^ 10) := by ring
          rw [h₁₁₈₄]
          have h₁₁₈₅ : (N : ℝ) * Real.log N ^ (c2 / 2) * Real.log N ^ c7 * (1 + Real.log N ^ 10) = (N : ℝ) * Real.log N ^ (c2 / 2 + c7) * (1 + Real.log N ^ 10) := by
            have h₁₁₈₅₁ : Real.log N ^ (c2 / 2) * Real.log N ^ c7 = Real.log N ^ (c2 / 2 + c7) := by
              rw [← Real.rpow_add (by linarith)]
              <;> ring_nf
            rw [h₁₁₈₅₁]
            <;> ring_nf
          rw [h₁₁₈₅]
          have h₁₁₈₆ : (N : ℝ) * Real.log N ^ (c2 / 2 + c7) * (1 + Real.log N ^ 10) ≤ (N : ℝ) * Real.log N ^ (c7 + c2 / 2 + 10) := by
            have h₁₁₈₆₁ : 1 + Real.log N ^ 10 ≤ 2 * Real.log N ^ 10 := by
              have h₁₁₈₆₂ : Real.log N ≥ 1 := by
                have h₁₁₈₆₃ : Real.log N ≥ Real.log 3 := Real.log_le_log (by positivity) (by
                  have h₁₁₈₆₄ : (N : ℝ) ≥ 3 := by exact_mod_cast (by linarith)
                  linarith)
                have h₁₁₈₆₅ : Real.log 3 ≥ 1 := by
                  have := Real.log_two_gt_d9
                  have := Real.log_two_lt_d9
                  norm_num at *
                  <;> linarith
                linarith
              have h₁₁₈₆₆ : Real.log N ^ 10 ≥ 1 := by
                apply one_le_rpow
                · linarith
                · norm_num
              nlinarith
            have h₁₁₈₆₂ : (N : ℝ) * Real.log N ^ (c2 / 2 + c7) * (1 + Real.log N ^ 10) ≤ (N : ℝ) * Real.log N ^ (c2 / 2 + c7) * (2 * Real.log N ^ 10) := by
              gcongr <;> nlinarith
            have h₁₁₈₆₃ : (N : ℝ) * Real.log N ^ (c2 / 2 + c7) * (2 * Real.log N ^ 10) = 2 * (N : ℝ) * Real.log N ^ (c2 / 2 + c7 + 10) := by
              have h₁₁₈₆₄ : Real.log N ^ (c2 / 2 + c7) * Real.log N ^ 10 = Real.log N ^ (c2 / 2 + c7 + 10) := by
                rw [← Real.rpow_add (by linarith)]
                <;> ring_nf
              calc
                (N : ℝ) * Real.log N ^ (c2 / 2 + c7) * (2 * Real.log N ^ 10) = 2 * (N : ℝ) * (Real.log N ^ (c2 / 2 + c7) * Real.log N ^ 10) := by ring
                _ = 2 * (N : ℝ) * Real.log N ^ (c2 / 2 + c7 + 10) := by rw [h₁₁₈₆₄] <;> ring
            have h₁₁₈₆₄ : 2 * (N : ℝ) * Real.log N ^ (c2 / 2 + c7 + 10) ≤ (N : ℝ) * Real.log N ^ (c7 + c2 / 2 + 10) := by
              have h₁₁₈₆₅ : (2 : ℝ) ≤ Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10)) := by
                have h₁₁₈₆₆ : (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10) : ℝ) = 0 := by ring
                rw [h₁₁₈₆₆]
                norm_num
                <;> linarith
              have h₁₁₈₆₆ : 0 < Real.log N := by linarith
              have h₁₁₈₆₇ : 0 < (N : ℝ) := by positivity
              have h₁₁₈₆₈ : 0 < Real.log N ^ (c2 / 2 + c7 + 10) := by positivity
              have h₁₁₈₆₉ : 2 * (N : ℝ) * Real.log N ^ (c2 / 2 + c7 + 10) ≤ (N : ℝ) * Real.log N ^ (c2 / 2 + c7 + 10) * Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10)) := by
                have h₁₁₈₆₁₀ : Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10)) ≥ 2 := by
                  have h₁₁₈₆₁₁ : (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10) : ℝ) = 0 := by ring
                  rw [h₁₁₈₆₁₁]
                  norm_num
                  <;> linarith
                have h₁₁₈₆₁₁ : 0 < Real.log N ^ (c2 / 2 + c7 + 10) := by positivity
                nlinarith
              have h₁₁₈₆₁₀ : (N : ℝ) * Real.log N ^ (c2 / 2 + c7 + 10) * Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10)) = (N : ℝ) * Real.log N ^ (c7 + c2 / 2 + 10) := by
                have h₁₁₈₆₁₁ : Real.log N ^ (c2 / 2 + c7 + 10) * Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10)) = Real.log N ^ (c7 + c2 / 2 + 10) := by
                  have h₁₁₈₆₁₂ : (c2 / 2 + c7 + 10 : ℝ) + (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10) : ℝ) = (c7 + c2 / 2 + 10 : ℝ) := by ring
                  have h₁₁₈₆₁₃ : Real.log N ^ (c2 / 2 + c7 + 10) * Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10)) = Real.log N ^ ((c2 / 2 + c7 + 10) + (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10))) := by
                    rw [← Real.rpow_add (by linarith)]
                    <;> ring_nf
                  rw [h₁₁₈₆₁₃]
                  <;> rw [h₁₁₈₆₁₂]
                  <;> ring_nf
                calc
                  (N : ℝ) * Real.log N ^ (c2 / 2 + c7 + 10) * Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10)) = (N : ℝ) * (Real.log N ^ (c2 / 2 + c7 + 10) * Real.log N ^ (c7 + c2 / 2 + 10 - (c2 / 2 + c7 + 10))) := by ring
                  _ = (N : ℝ) * Real.log N ^ (c7 + c2 / 2 + 10) := by rw [h₁₁₈₆₁₁]
                  _ = (N : ℝ) * Real.log N ^ (c7 + c2 / 2 + 10) := by ring
              linarith
            linarith
          linarith
        linarith
      
      -- Define H' = max (H269) (|T1|^(1/3)) and ensure H' ≥ 2
      have h₁₂ : ∀ (β T1 : ℝ), 1 / 2 ≤ β → β ≤ 5 / 6 → |T1| ≤ 2 * T269 N A lam q c7 → (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ (max (K23 + 1) 1 : ℝ) * Real.log N ^ (-B - 1) := by
        intro β T1 hβ0 hβ1 hT1
        have h₁₂₁ : 0 < (N : ℝ) := by positivity
        have h₁₂₂ : 0 < Real.log N := by linarith
        have h₁₂₃ : 1 ≤ Real.log N := by linarith
        have h₁₂₄ : 0 < A := by positivity
        have h₁₂₅ : 0 < (q : ℝ) := by positivity
        -- Define H' = max (H269 N A lam) (|T1|^(1/3))
        have h₁₂₆ : H269 N A lam ≥ 10 := by
          have h₁₂₆₁ : H269 N A lam = 10 * ((N : ℝ) / A + |lam| * A) := by
            simp [H269]
            <;> ring_nf
          rw [h₁₂₆₁]
          have h₁₂₆₂ : (N : ℝ) / A ≥ 1 := by
            have h₁₂₆₃ : A ≤ N := hAN
            have h₁₂₆₄ : 0 < A := by positivity
            have h₁₂₆₅ : 0 < (N : ℝ) := by positivity
            have h₁₂₆₆ : (N : ℝ) / A ≥ 1 := by
              rw [ge_iff_le]
              rw [le_div_iff (by positivity)]
              nlinarith
            exact h₁₂₆₆
          have h₁₂₆₃ : |lam| * A ≥ 0 := by positivity
          nlinarith
        have h₁₂₇ : 0 ≤ |T1| := abs_nonneg T1
        have h₁₂₈ : 0 ≤ |T1| ^ (1 / 3 : ℝ) := by positivity
        -- Define H' = max (H269 N A lam) (|T1|^(1/3))
        let H' : ℝ := max (H269 N A lam) (|T1| ^ (1 / 3 : ℝ))
        have h₁₂₉ : H' ≥ 2 := by
          have h₁₂₉₁ : H269 N A lam ≥ 10 := h₁₂₆
          have h₁₂₉₂ : H' = max (H269 N A lam) (|T1| ^ (1 / 3 : ℝ)) := rfl
          have h₁₂₉₃ : H' ≥ H269 N A lam := by
            rw [h₁₂₉₂]
            apply le_max_left
          linarith
        have h₁₃₀ : |T1| ^ (1 / 3 : ℝ) ≤ H' := by
          have h₁₃₀₁ : H' = max (H269 N A lam) (|T1| ^ (1 / 3 : ℝ)) := rfl
          rw [h₁₃₀₁]
          apply le_max_right
        have h₁₃₁ : H269 N A lam ≤ H' := by
          have h₁₃₁₁ : H' = max (H269 N A lam) (|T1| ^ (1 / 3 : ℝ)) := rfl
          rw [h₁₃₁₁]
          apply le_max_left
        -- Apply h23 with α = β, T = T1, H = H'
        have h₁₃₂ : zeroCountZ β T1 H' q ≤ K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ) := by
          have h₁₃₂₁ : 2 ≤ H' := by linarith
          have h₁₃₂₂ : |T1| ^ (1 / 3 : ℝ) ≤ H' := h₁₃₀
          have h₁₃₂₃ : 1 / 2 ≤ β := hβ0
          have h₁₃₂₄ : β ≤ 1 := by linarith
          have h₁₃₂₅ : zeroCountZ β T1 H' q ≤ K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ) := by
            have h₁₃₂₆ := hK23 q (by infer_instance) β T1 H' h₁₃₂₁ h₁₃₂₂ h₁₃₂₃ h₁₃₂₄
            exact h₁₃₂₆
          exact h₁₃₂₅
        -- Use monotonicity of zeroCountZ in H
        have h₁₃₃ : zeroCountZ β T1 (H269 N A lam) q ≤ zeroCountZ β T1 H' q := by
          apply zeroCountZ_mono_H
          <;> linarith
        -- Combine to get bound on zeroCountZ β T1 (H269 N A lam) q
        have h₁₃₄ : zeroCountZ β T1 (H269 N A lam) q ≤ K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ) := by
          linarith
        -- Multiply by N^(β-1)
        have h₁₃₅ : (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ (N : ℝ) ^ (β - 1) * (K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ)) := by
          have h₁₃₅₁ : 0 ≤ (N : ℝ) ^ (β - 1) := by positivity
          have h₁₃₅₂ : 0 ≤ zeroCountZ β T1 (H269 N A lam) q := zeroCountZ_nonneg β T1 (H269 N A lam) q
          have h₁₃₅₃ : 0 ≤ K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ) := by positivity
          nlinarith
        -- Now we need to bound the RHS by (max (K23 + 1) 1) * Real.log N ^ (-B - 1)
        have h₁₃₆ : (N : ℝ) ^ (β - 1) * (K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ)) ≤ (max (K23 + 1) 1 : ℝ) * Real.log N ^ (-B - 1) := by
          have h₁₃₆₁ : (N : ℝ) ^ (β - 1) * (K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ)) = K23 * ((q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ)) ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ) := by
            have h₁₃₆₁₁ : 0 < (N : ℝ) := by positivity
            have h₁₃₆₁₂ : 0 < (q : ℝ) := by positivity
            have h₁₃₆₁₃ : 0 < H' := by
              have h₁₃₆₁₄ : H' = max (H269 N A lam) (|T1| ^ (1 / 3 : ℝ)) := rfl
              have h₁₃₆₁₅ : H269 N A lam ≥ 10 := h₁₂₆
              have h₁₃₆₁₆ : H' ≥ H269 N A lam := by
                rw [h₁₃₆₁₄]
                apply le_max_left
              linarith
            have h₁₃₆₁₇ : 0 < (q : ℝ) * H' := by positivity
            have h₁₃₆₁₈ : 0 < (N : ℝ) ^ (3 / 8 : ℝ) := by positivity
            have h₁₃₆₁₉ : (N : ℝ) ^ (β - 1) = (N : ℝ) ^ (-(1 - β)) := by
              have h₁₃₆₁₉₁ : (β - 1 : ℝ) = -(1 - β) := by ring
              rw [h₁₃₆₁₉₁]
            rw [h₁₃₆₁₉]
            have h₁₃₆₂₀ : (N : ℝ) ^ (-(1 - β)) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) = ((q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ)) ^ (8 / 3 * (1 - β)) := by
              have h₁₃₆₂₀₁ : (N : ℝ) ^ (-(1 - β)) = ((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-(8 / 3 * (1 - β))) := by
                have h₁₃₆₂₀₂ : (-(1 - β) : ℝ) = (3 / 8 : ℝ) * (-(8 / 3 * (1 - β))) := by ring
                rw [h₁₃₆₂₀₂]
                rw [← Real.rpow_mul (by positivity)]
                <;> ring_nf
                <;> field_simp
                <;> ring_nf
              rw [h₁₃₆₂₀₁]
              have h₁₃₆₂₀₃ : ((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-(8 / 3 * (1 - β))) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) = ((q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ)) ^ (8 / 3 * (1 - β)) := by
                have h₁₃₆₂₀₄ : 0 < (N : ℝ) ^ (3 / 8 : ℝ) := by positivity
                have h₁₃₆₂₀₅ : 0 < (q : ℝ) * H' := by positivity
                have h₁₃₆₂₀₆ : ((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-(8 / 3 * (1 - β))) = ((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-(8 / 3 * (1 - β))) := rfl
                calc
                  ((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-(8 / 3 * (1 - β))) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) = (((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-1)) ^ (8 / 3 * (1 - β)) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) := by
                    rw [show (-(8 / 3 * (1 - β)) : ℝ) = (-1 : ℝ) * (8 / 3 * (1 - β)) by ring]
                    rw [← Real.rpow_mul (by positivity)]
                    <;> ring_nf
                  _ = (((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-1) * ((q : ℝ) * H')) ^ (8 / 3 * (1 - β)) := by
                    rw [← Real.mul_rpow (by positivity) (by positivity)]
                    <;> ring_nf
                  _ = ((q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ)) ^ (8 / 3 * (1 - β)) := by
                    have h₁₃₆₂₀₇ : ((N : ℝ) ^ (3 / 8 : ℝ)) ^ (-1) = 1 / (N : ℝ) ^ (3 / 8 : ℝ) := by
                      rw [Real.rpow_neg (by positivity)]
                      <;> field_simp
                    rw [h₁₃₆₂₀₇]
                    <;> field_simp [h₁₃₆₁₈.ne']
                    <;> ring_nf
              rw [h₁₃₆₂₀₃]
            calc
              (N : ℝ) ^ (-(1 - β)) * (K23 * ((q : ℝ) * H') ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ)) = K23 * ((N : ℝ) ^ (-(1 - β)) * ((q : ℝ) * H') ^ (8 / 3 * (1 - β))) * Real.log ((q : ℝ) * H') ^ (216 : ℝ) := by ring
              _ = K23 * ((q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ)) ^ (8 / 3 * (1 - β)) * Real.log ((q : ℝ) * H') ^ (216 : ℝ) := by rw [h₁₃₆₂₀]
          have h₁₃₆₂ : (q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ) ≤ Real.log N ^ (-(c1 + c2 + (9 / 4 : ℝ) * (B + 218)) + c1 + c2) := by sorry
          have h₁₃₆₃ : (q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ) ≤ Real.log N ^ (-(9 / 4 : ℝ) * (B + 218)) := by sorry
          have h₁₃₆₄ : ((q : ℝ) * H' / (N : ℝ) ^ (3 / 8 : ℝ)) ^ (8 / 3 * (1 - β)) ≤ Real.log N ^ (-(B + 218)) := by sorry
          have h₁₃₆₅ : Real.log ((q : ℝ) * H') ≤ Real.log N + Real.log (Real.log N) + 10 := by sorry
          have h₁₃₆₆ : Real.log ((q : ℝ) * H') ^ (216 : ℝ) ≤ (Real.log N + Real.log (Real.log N) + 10) ^ (216 : ℝ) := by sorry
          have h₁₃₆₇ : (Real.log N + Real.log (Real.log N) + 10) ^ (216 : ℝ) ≤ Real.log N ^ (216 + 1) := by sorry
          have h₁₃₆₈ : K23 * Real.log N ^ (-(B + 218)) * Real.log N ^ (216 + 1) ≤ (max (K23 + 1) 1 : ℝ) * Real.log N ^ (-B - 1) := by sorry
          sorry
        -- Final step
        have h₁₃₇ : (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ (max (K23 + 1) 1 : ℝ) * Real.log N ^ (-B - 1) := by
          linarith
        exact h₁₃₇
      -- Final step
      have h₁₃ : (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ (max (K23 + 1) 1 : ℝ) * Real.log N ^ (-B - 1) := h₁₂ β T1 hβ0 hβ1 hT1
      have h₁₄ : (max (K23 + 1) 1 : ℝ) * Real.log N ^ (-B - 1) ≤ (max (max (K23 + 1) 1) (max N₀_log 3) : ℝ) * Real.log N ^ (-B - 1) := by
        have h₁₄₁ : (max (K23 + 1) 1 : ℝ) ≤ (max (max (K23 + 1) 1) (max N₀_log 3) : ℝ) := by apply le_max_left
        have h₁₄₂ : 0 ≤ Real.log N ^ (-B - 1) := Real.rpow_nonneg (by linarith) _
        nlinarith
      linarith
  -- Convert h_main to the required form
  obtain ⟨c3, hc3, K, N₀, h_main'⟩ := h_main
  refine' ⟨c3, hc3, K, N₀, _⟩
  intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
  have h₁ := h_main' N A α lam a q (by infer_instance) hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
  exact h₁

/-- LEAF: Page 269, the display after "For 5/6 ≤ β ≤ 1, by (2.4) and Lemma 5": the high range
of (3.19), `N^{β-1} N(β, T₁, H, q) ≪ (q^{12/5} H^{12/5} N⁻¹)^{1-β} L^{c₀} ≪ exp(-c₀ L^{1/5})`.
MEDIUM. Apply Lemma 5 at height `N`, where `q ≤ L^{c₂} = (log N)^{c₂}`: the count is zero for
`β ≥ 1 - c₀/(log q + (log (N + 2))^{4/5})`, so `1 - β ≫ L^{-4/5}` on the remaining range. -/
theorem display319_high_of_24 (h24 : Lemma4Eq24) (h5 : Lemma5NoExc) :
    Display319On (5 / 6) 1 := by
  sorry

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
