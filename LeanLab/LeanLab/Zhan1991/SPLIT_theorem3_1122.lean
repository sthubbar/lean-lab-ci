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
theorem display319_low_of_23 (h23 : Lemma4Eq23) (h5 : Lemma5NoExc) :
    Display319On (1 / 2) (5 / 6) := by
  sorry

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
