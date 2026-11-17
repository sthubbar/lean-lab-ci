import LeanLab.LanguascoPerelli1996.Theorem2Data597
import LeanLab.LanguascoPerelli1996.Arithmetic597

/-!
P0071 pages 353 and 354, Theorem 2, and page 359, corrected log fourth power.
KPP1993 pages 279 through 281, displays 12 through 18.
KPP1995 corrigendum pages 215 and 216, corrected display 18.
All analytic admissions are named cited leaves.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp597a
open Real Filter Topology ArithmeticFunction MeasureTheory Finset

/-- P0071 page 353, P equals Q times log to minus ten of X. -/
noncomputable def cutoff (X Q : ℝ) : ℝ := Q / Real.log X ^ 10

/-- P0071 page 353, the even integers in the short interval. -/
noncomputable def evenInterval (X H : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈X⌉₊ ⌊X + H⌋₊).filter Even

/-- KPP1993 page 277, translated reduced Farey fractions of bounded denominator. -/
noncomputable def fareyPoints (N : ℕ) : Finset ℚ :=
  (Finset.Icc 1 N).biUnion fun q =>
    ((Finset.Icc (-(q : ℤ)) (2 * q)).filter fun a => a.natAbs.Coprime q).image
      fun a : ℤ => (a : ℚ) / q

/-- KPP1993 page 277, predecessor in the translated Farey sequence. -/
noncomputable def fareyPrev (N : ℕ) (r : ℚ) : ℚ :=
  let s := (fareyPoints N).filter fun t => t < r
  if h : s.Nonempty then s.max' h else r - 1

/-- KPP1993 page 277, successor in the translated Farey sequence. -/
noncomputable def fareyNext (N : ℕ) (r : ℚ) : ℚ :=
  let s := (fareyPoints N).filter fun t => r < t
  if h : s.Nonempty then s.min' h else r + 1

/-- KPP1993 page 277, the mediant endpoint between adjacent reduced fractions. -/
def mediant (r s : ℚ) : ℚ :=
  (r.num + s.num : ℤ) / ((r.den + s.den : ℕ) : ℚ)

/-- P0071 page 353, one actual Farey arc coefficient of the stopped S squared. -/
noncomputable def arcCoefficient (X Q : ℝ) (m : ℕ) (r : ℚ) : ℂ :=
  ∫ α in (mediant (fareyPrev ⌊Q⌋₊ r) r : ℝ)..(mediant r (fareyNext ⌊Q⌋₊ r) : ℝ),
    S X α ^ 2 * e (-(m : ℝ) * α)

/-- P0071 page 353, the major arc coefficient over reduced centers from zero inclusive to one exclusive. -/
noncomputable def majorCoefficient (X Q : ℝ) (m : ℕ) : ℂ :=
  ∑ r ∈ (fareyPoints ⌊Q⌋₊).filter (fun r => 0 ≤ r ∧ r < 1 ∧ (r.den : ℝ) ≤ cutoff X Q),
    arcCoefficient X Q m r

/-- P0071 page 353, the full Fourier coefficient of the actual stopped S squared. -/
noncomputable def fullCoefficient (X : ℝ) (m : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1, S X α ^ 2 * e (-(m : ℝ) * α)

/-- P0071 page 353, complementary minor arc coefficient after one period is dissected. -/
noncomputable def minorCoefficient (X Q : ℝ) (m : ℕ) : ℂ :=
  fullCoefficient X m - majorCoefficient X Q m

/-- P0071 page 353, the actual stopped integer representation count I of m. -/
noncomputable def representationCount (X : ℝ) (m : ℕ) : ℕ :=
  (((Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊) ×ˢ (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊)).filter
    fun p => p.1 + p.2 = m).card

/-- KPP1993 page 277 display 3, Ramanujan sum at minus m. -/
noncomputable def ramanujan (q m : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), e (-(m : ℝ) * a / q)

/-- KPP1993 page 279 display 11, actual Ramanujan singular series tail. -/
noncomputable def tail (P : ℝ) (m : ℕ) : ℂ :=
  ∑' q : ℕ, if P < (q : ℝ) then (muPhi q : ℂ) ^ 2 * ramanujan q m else 0

/-- P0071 page 353, the stopped representation count times the full Ramanujan series. -/
noncomputable def mainTerm (X : ℝ) (m : ℕ) : ℂ :=
  (representationCount X m : ℂ) * ∑' q : ℕ, (muPhi q : ℂ) ^ 2 * ramanujan q m

/-- KPP1993 page 279 display 11 and P0071 page 353 display 8, the exact major arc error. -/
noncomputable def majorError (X Q : ℝ) (m : ℕ) : ℂ :=
  mainTerm X m - (representationCount X m : ℂ) * tail (cutoff X Q) m - majorCoefficient X Q m

/-- KPP1993 page 280 display 14, the large divisor envelope. -/
noncomputable def largeDivisor (P : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d : ℕ => Squarefree d ∧ P < (d : ℝ)), 1 / (Nat.totient d : ℝ)

/-- KPP1993 page 280 display 14, the small divisor envelope including its inverse P factor. -/
noncomputable def smallDivisor (P : ℝ) (m : ℕ) : ℝ :=
  (1 / P) * ∑ d ∈ m.divisors.filter (fun d : ℕ => Squarefree d ∧ (d : ℝ) ≤ P), (d : ℝ) / Nat.totient d

/-- P0071 page 353 display 7, exact coefficient identity behind KPP1993 display 13. -/
theorem coefficient_split (X Q : ℝ) (m : ℕ) :
    fullCoefficient X m - mainTerm X m + majorError X Q m =
      minorCoefficient X Q m - (representationCount X m : ℂ) * tail (cutoff X Q) m := by
  unfold majorError minorCoefficient
  ring

/-- P0071 page 353 display 7, the proved finite norm split with its implicit constant two. -/
theorem display13 (X Q H : ℝ) :
    ∑ m ∈ evenInterval X H, ‖fullCoefficient X m - mainTerm X m + majorError X Q m‖ ^ 2 ≤
      2 * (∑ m ∈ evenInterval X H, ‖minorCoefficient X Q m‖ ^ 2) +
      2 * ∑ m ∈ evenInterval X H,
        ‖(representationCount X m : ℂ) * tail (cutoff X Q) m‖ ^ 2 :=
  Arithmetic597.display13 _ _ _ _ _ _ (fun m _ => coefficient_split X Q m)

/-- LEAF KPP1993 page 280 display 14, Ramanujan tail reduction to the two divisor envelopes.
The absolute convergence and squarefree Ramanujan identity remain cited. -/
theorem ramanujan_divisor_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℝ, Real.exp 1 ≤ P → ∀ m : ℕ, 0 < m →
      ‖tail P m‖ ≤ C * (largeDivisor P m + smallDivisor P m) := by
  sorry

/-- LEAF KPP1993 page 280 display 15, large divisor second moment after dyadic summation. -/
theorem large_divisor_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X H P : ℝ, 4 ≤ X → 2 ≤ H → H ≤ X →
      Real.exp 1 ≤ P → P ^ 2 ≤ H →
      ∑ m ∈ evenInterval X H, largeDivisor P m ^ 2 ≤
        C * (H * Real.log P / P ^ 2 + Real.log X ^ 2) := by
  sorry

/-- LEAF KPP1993 page 280 display 16, small divisor second moment after the lcm sum. -/
theorem small_divisor_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X H P : ℝ, 4 ≤ X → 2 ≤ H → H ≤ X →
      Real.exp 1 ≤ P → P ^ 2 ≤ H →
      ∑ m ∈ evenInterval X H, smallDivisor P m ^ 2 ≤
        C * H * Real.log P ^ 3 / P ^ 2 := by
  sorry

/-- KPP1993 pages 279 and 280 Lemma 2, conditional only on its three named arithmetic leaves. -/
theorem lemma2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X H P : ℝ, 4 ≤ X → 2 ≤ H → H ≤ X →
      Real.exp 1 ≤ P → P ^ 2 ≤ H →
      ∑ m ∈ evenInterval X H, ‖tail P m‖ ^ 2 ≤
        C * (H * Real.log P ^ 3 / P ^ 2 + Real.log X ^ 2) := by
  obtain ⟨A, hA, ha⟩ := ramanujan_divisor_envelope
  obtain ⟨B, hB, hb⟩ := large_divisor_moment
  obtain ⟨C, hC, hc⟩ := small_divisor_moment
  refine ⟨2 * A ^ 2 * (B + C), by positivity, ?_⟩
  intro X H P hX hH hHX hP hPH
  have hX0 : 0 ≤ X := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hP0 : 0 < P := (Real.exp_pos 1).trans_le hP
  have hlog : 1 ≤ Real.log P := by
    have := Real.log_le_log (Real.exp_pos 1) hP
    simpa only [Real.log_exp] using this
  have hlog3 : Real.log P ≤ Real.log P ^ 3 := by
    simpa using pow_le_pow_right₀ hlog (by norm_num : 1 ≤ 3)
  have hlarge : (∑ m ∈ evenInterval X H, largeDivisor P m ^ 2) ≤
      B * (H * Real.log P ^ 3 / P ^ 2 + Real.log X ^ 2) := by
    refine (hb X H P hX hH hHX hP hPH).trans ?_
    gcongr
  have hsmall : (∑ m ∈ evenInterval X H, smallDivisor P m ^ 2) ≤
      C * (H * Real.log P ^ 3 / P ^ 2 + Real.log X ^ 2) := by
    have hh := hc X H P hX hH hHX hP hPH
    calc
      _ ≤ C * (H * Real.log P ^ 3 / P ^ 2) := by simpa only [mul_div_assoc, mul_assoc] using hh
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hC
  have hh := Arithmetic597.lemma2_arithmetic (evenInterval X H) (tail P)
    (largeDivisor P) (smallDivisor P)
    (fun m hm => ha P hP m (by
      have hmX : X ≤ (m : ℝ) := Nat.ceil_le.mp (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      exact_mod_cast (show (0 : ℝ) < m by linarith))) hlarge hsmall
  convert hh using 1; ring

/-- P0071 page 353, the stopped integer representation count is at most 2X. -/
theorem representationCount_le {X : ℝ} (hX : 4 ≤ X) (m : ℕ) :
    (representationCount X m : ℝ) ≤ 2 * X := by
  let s := (((Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊) ×ˢ (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊)).filter
    fun p => p.1 + p.2 = m)
  have hc : s.card ≤ (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq heq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      apply Prod.ext heq
      omega
  have hceil : 1 ≤ ⌈X / 4⌉₊ := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hcard : (Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊).card ≤ ⌊2 * X⌋₊ := by
    rw [Nat.card_Icc]
    omega
  have hh : representationCount X m ≤ ⌊2 * X⌋₊ := hc.trans hcard
  have hhR : (representationCount X m : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hh
  exact hhR.trans (Nat.floor_le (by linarith : 0 ≤ 2 * X))

/-- P0071 page 353 before display 7, the actual stopped representation count has size at least X over four. -/
theorem representationCount_lower {X : ℝ} (hX : 16 ≤ X) {m : ℕ}
    (hmX : X ≤ (m : ℝ)) (hm2X : (m : ℝ) ≤ 2 * X) :
    X / 4 ≤ (representationCount X m : ℝ) := by
  let l := ⌈X / 4⌉₊
  let b := ⌊2 * X⌋₊
  have hlR : (l : ℝ) < X / 4 + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ X / 4)
  have hml : 2 * l ≤ m := by
    have hh : (2 : ℝ) * l ≤ m := by linarith
    exact_mod_cast hh
  have hmb : m ≤ b := Nat.le_floor hm2X
  have heq : representationCount X m = (Finset.Icc l (m - l)).card := by
    unfold representationCount
    change (((Finset.Icc l b ×ˢ Finset.Icc l b).filter fun p => p.1 + p.2 = m).card) = _
    symm
    apply Finset.card_bij (fun n _ => (n, m - n))
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      have hn0 : n ≤ m := by omega
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega
      · simp only
        omega
    · intro n hn k hk he
      exact congrArg Prod.fst he
    · intro p hp
      obtain ⟨hp, hsum⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hp1l, hp1b⟩ := Finset.mem_Icc.mp hp1
      obtain ⟨hp2l, hp2b⟩ := Finset.mem_Icc.mp hp2
      refine ⟨p.1, Finset.mem_Icc.mpr ⟨hp1l, by omega⟩, ?_⟩
      apply Prod.ext
      · rfl
      · simp only
        omega
  have hcount : representationCount X m = m + 1 - 2 * l := by
    rw [heq, Nat.card_Icc]
    omega
  have hs : 2 * l ≤ m + 1 := by omega
  rw [hcount, Nat.cast_sub hs]
  push_cast
  linarith

/-- KPP1993 page 281 display 17 in the stopped normalization of P0071 page 353. -/
theorem display17 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X H P : ℝ, 4 ≤ X → 2 ≤ H → H ≤ X →
      Real.exp 1 ≤ P → P ^ 2 ≤ H →
      ∑ m ∈ evenInterval X H, ‖(representationCount X m : ℂ) * tail P m‖ ^ 2 ≤
        C * X ^ 2 * (H * Real.log P ^ 3 / P ^ 2 + Real.log X ^ 2) := by
  obtain ⟨C, hC, hc⟩ := lemma2
  refine ⟨4 * C, by positivity, ?_⟩
  intro X H P hX hH hHX hP hPH
  have hh := Arithmetic597.display17 (evenInterval X H)
    (fun m => (representationCount X m : ℝ)) (tail P)
    (fun m _ => by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact representationCount_le hX m)
    (hc X H P hX hH hHX hP hPH)
  simpa only [Complex.ofReal_natCast] using (show
      (∑ m ∈ evenInterval X H, ‖((representationCount X m : ℝ) : ℂ) * tail P m‖ ^ 2) ≤
        (4 * C) * X ^ 2 * (H * Real.log P ^ 3 / P ^ 2 + Real.log X ^ 2) by nlinarith [hh])

/-- LEAF P0071 page 353 display 8, corrected KPP1993 display 12.
The general character Lemma 1 has log fourth power, as corrected on P0071 page 359.
Its major arc error is sqrt of P over Q times X log squared X plus P Q.
With P equal to Q over log to the ten this is at most a constant times X over log cubed X. -/
theorem corrected_major_arc_raw :
    GRH → ∃ A B X0 : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ X Q : ℝ, X0 ≤ X → 16 ≤ X →
      Real.exp 1 ≤ cutoff X Q → Q ≤ X ^ (1 / 2 : ℝ) / 2 →
      ∀ m ∈ evenInterval X (4 * Q ^ 2), ‖majorError X Q m‖ ≤
        A * Real.sqrt (cutoff X Q / Q * Real.log X ^ 4) * X + B * cutoff X Q * Q := by
  sorry

/-- P0071 page 353 display 8, parameter arithmetic using the corrected log fourth power input. -/
theorem corrected_major_arc :
    GRH → ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ X Q : ℝ, X0 ≤ X → 16 ≤ X →
      Real.exp 1 ≤ cutoff X Q → Q ≤ X ^ (1 / 2 : ℝ) / 2 →
      ∀ m ∈ evenInterval X (4 * Q ^ 2), ‖majorError X Q m‖ ≤ C * X / Real.log X ^ 3 := by
  intro hGRH
  obtain ⟨A, B, X0, hA, hB, hh⟩ := corrected_major_arc_raw hGRH
  refine ⟨A + B, X0, by positivity, ?_⟩
  intro X Q hX0 hX hP hQ m hm
  have hXpos : 0 < X := by linarith
  have hlog : 1 ≤ Real.log X := by
    have he : Real.exp 1 ≤ X := le_trans Real.exp_one_lt_three.le (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hQpos : 0 < Q := by
    have hPc : 0 < Q / Real.log X ^ 10 := (Real.exp_pos 1).trans_le hP
    exact (div_pos_iff_of_pos_right (by positivity : 0 < Real.log X ^ 10)).mp hPc
  have hQQ : Q ^ 2 ≤ X := by
    have := Arithmetic597.short_interval_geometry hXpos.le hQpos.le hQ
    nlinarith
  have hPpos : 0 < cutoff X Q := (Real.exp_pos 1).trans_le hP
  have hsqrt : Real.sqrt (cutoff X Q / Q * Real.log X ^ 4) =
      Real.sqrt (cutoff X Q / Q) * Real.log X ^ 2 := by
    rw [Real.sqrt_mul (div_nonneg hPpos.le hQpos.le),
      show Real.log X ^ 4 = (Real.log X ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hraw := hh X Q hX0 hX hP hQ m hm
  rw [hsqrt] at hraw
  apply Arithmetic597.corrected_display12_scalar (P := cutoff X Q) hXpos.le hQpos hlog hA hB hQQ rfl
  convert hraw using 1 <;> ring

/-- LEAF P0071 page 353 display 9 from KPP1993 page 281 display 18.
The corrected Fejer kernel argument is in the 1995 corrigendum pages 215 and 216.
The elementary T term is included as the additive X to two plus delta contribution. -/
theorem corrected_display18 :
    GRH → ∀ δ : ℝ, 0 < δ → ∃ C X0 : ℝ, 0 ≤ C ∧
      ∀ X Q M : ℝ, X0 ≤ X → 16 ≤ X → Real.exp 1 ≤ cutoff X Q →
      Q ≤ X ^ (1 / 2 : ℝ) / 2 → 0 ≤ M →
      (∀ (q : ℕ) [NeZero q], cutoff X Q < (q : ℝ) → (q : ℝ) ≤ Q →
        ∀ a : ℕ, a.Coprime q → Ival X Q q a ≤ M) →
      ∑ m ∈ evenInterval X (4 * Q ^ 2), ‖minorCoefficient X Q m‖ ^ 2 ≤
        C * (4 * Q ^ 2 * X * Real.log X * M + X ^ (2 + δ)) := by
  sorry

/-- LEAF P0071 page 354 after display 10, the standard exceptional integer argument.
This includes the singular series lower bound and removal of proper prime power representations.
The Fourier coefficient is for the actual stopped Lambda polynomial and EH counts prime sums. -/
theorem exceptional_energy_lower :
    ∀ B : ℝ, 0 ≤ B → ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ X H : ℝ,
      X0 ≤ X → 16 ≤ X → 0 ≤ H → H ≤ X → ∀ f : ℕ → ℂ,
      (∀ m ∈ evenInterval X H, ‖f m‖ ≤ B * X / Real.log X ^ 3) →
      (EH X H : ℝ) * X ^ 2 ≤ C *
        ∑ m ∈ evenInterval X H, ‖fullCoefficient X m - mainTerm X m + f m‖ ^ 2 := by
  sorry

/-- P0071 page 353, the cutoff tends past exp of one uniformly in the allowed Q range. -/
theorem eventual_cutoff {ε0 : ℝ} (hε0 : 0 < ε0) (Q : ℝ → ℝ)
    (hQ : ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → X ^ ε0 ≤ Q X ∧ Q X ≤ X ^ (1 / 2 : ℝ) / 2) :
    ∀ᶠ X : ℝ in atTop,
      16 ≤ X ∧ 1 ≤ Real.log X ∧ 0 < Q X ∧ Real.exp 1 ≤ cutoff X (Q X) ∧
      cutoff X (Q X) ≤ Q X ∧ Q X ≤ X ∧ Real.log (cutoff X (Q X)) ≤ Real.log X ∧
      2 ≤ 4 * Q X ^ 2 ∧ 4 * Q X ^ 2 ≤ X ∧ cutoff X (Q X) ^ 2 ≤ 4 * Q X ^ 2 := by
  obtain ⟨X1, hRange⟩ := hQ
  have hh : 0 < ε0 / 2 := by positivity
  filter_upwards [eventually_ge_atTop X1, eventually_ge_atTop (16 : ℝ),
    Arithmetic597.eventually_log_pow_le_rpow 10 hh,
    (tendsto_rpow_atTop hh).eventually_ge_atTop (Real.exp 1)] with X hX1 hX hlogpow hpow
  obtain ⟨hlo, hhi⟩ := hRange X hX1
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hlog : 1 ≤ Real.log X := by
    have he : Real.exp 1 ≤ X := le_trans Real.exp_one_lt_three.le (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hQpos : 0 < Q X := (Real.rpow_pos_of_pos hXpos _).trans_le hlo
  have hLpos : 0 < Real.log X ^ 10 := by positivity
  have hpowmul : X ^ (ε0 / 2) * X ^ (ε0 / 2) = X ^ ε0 := by
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  have hcut : Real.exp 1 ≤ cutoff X (Q X) := by
    apply (le_div_iff₀ hLpos).2
    calc
      _ ≤ X ^ (ε0 / 2) * X ^ (ε0 / 2) :=
        mul_le_mul hpow hlogpow (by positivity) (by positivity)
      _ = X ^ ε0 := hpowmul
      _ ≤ Q X := hlo
  have hLone : 1 ≤ Real.log X ^ 10 := one_le_pow₀ hlog
  have hPQ : cutoff X (Q X) ≤ Q X := by
    exact div_le_self hQpos.le hLone
  have hQX : Q X ≤ X := by
    have hroot : X ^ (1 / 2 : ℝ) ≤ X := by
      simpa using Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1 / 2 : ℝ) ≤ 1)
    linarith
  have hPpos : 0 < cutoff X (Q X) := (Real.exp_pos 1).trans_le hcut
  have hlogP : Real.log (cutoff X (Q X)) ≤ Real.log X :=
    Real.log_le_log hPpos (hPQ.trans hQX)
  have hQone : 1 ≤ Q X := (le_trans (by linarith [Real.exp_one_gt_two] : (1 : ℝ) ≤ Real.exp 1) hcut).trans hPQ
  have hH : 4 * Q X ^ 2 ≤ X := Arithmetic597.short_interval_geometry hXpos.le hQpos.le hhi
  exact ⟨hX, hlog, hQpos, hcut, hPQ, hQX, hlogP, by nlinarith, hH, by nlinarith⟩

/-- P0071 page 353 display 9, Bound5 at minor denominators supplies one uniform envelope. -/
theorem minor_remainder_envelope {Q : ℝ → ℝ} (h5 : Bound5 Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 0 < X → 0 < Q X → 0 < cutoff X (Q X) →
      ∀ (q : ℕ) [NeZero q], cutoff X (Q X) < (q : ℝ) → (q : ℝ) ≤ Q X →
      ∀ a : ℕ, a.Coprime q →
        Ival X (Q X) q a ≤ B * X ^ (1 + δ) / (cutoff X (Q X) * Q X) := by
  obtain ⟨C, X0, hc⟩ := h5 δ hδ
  refine ⟨max C 0, X0, le_max_right _ _, ?_⟩
  intro X hX hXpos hQpos hPpos q inst hPq hq a ha
  calc
    _ ≤ C * X ^ (1 + δ) / (q * Q X) := hc X hX q hq a ha
    _ ≤ max C 0 * X ^ (1 + δ) / (q * Q X) := by
      gcongr
      exact le_max_left _ _
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (mul_pos hPpos hQpos) (by nlinarith)

/-- P0071 pages 353 and 354 displays 7 through 10, conditional on the named arithmetic and display 18 leaves. -/
theorem energy_bound (hGRH : GRH) {ε0 : ℝ} (hε0 : 0 < ε0) (Q : ℝ → ℝ)
    (hQ : ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → X ^ ε0 ≤ Q X ∧ Q X ≤ X ^ (1 / 2 : ℝ) / 2)
    (h5 : Bound5 Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D X0 : ℝ, 0 ≤ D ∧ ∀ X : ℝ, X0 ≤ X →
      (∑ m ∈ evenInterval X (4 * Q X ^ 2),
        ‖fullCoefficient X m - mainTerm X m + majorError X (Q X) m‖ ^ 2) ≤
          D * X ^ (2 + δ) * Real.log X ^ 23 := by
  obtain ⟨B, Xb, hB, hb⟩ := minor_remainder_envelope h5 hδ
  obtain ⟨C, Xc, hC, hc⟩ := corrected_display18 hGRH δ hδ
  obtain ⟨D, hD, hd⟩ := display17
  obtain ⟨Xq, hq⟩ := hQ
  let K := 2 * C * (4 * B + 1) + 10 * D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  suffices ∀ᶠ X : ℝ in atTop,
      (∑ m ∈ evenInterval X (4 * Q X ^ 2),
        ‖fullCoefficient X m - mainTerm X m + majorError X (Q X) m‖ ^ 2) ≤
          K * X ^ (2 + δ) * Real.log X ^ 23 by
    obtain ⟨X0, hX0⟩ := eventually_atTop.1 this
    exact ⟨K, X0, hK, hX0⟩
  filter_upwards [eventual_cutoff hε0 Q ⟨Xq, hq⟩, eventually_ge_atTop Xb,
    eventually_ge_atTop Xc, eventually_ge_atTop Xq] with X hgeom hXb hXc hXq
  rcases hgeom with ⟨hX, hL, hQpos, hP, hPQ, hQX, hlogP, hH, hHX, hPH⟩
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hPpos : 0 < cutoff X (Q X) := (Real.exp_pos 1).trans_le hP
  have hlogP0 : 0 ≤ Real.log (cutoff X (Q X)) := by
    have he : 1 ≤ cutoff X (Q X) := le_trans (by linarith [Real.exp_one_gt_two]) hP
    exact Real.log_nonneg he
  let M := B * X ^ (1 + δ) / (cutoff X (Q X) * Q X)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hminor0 := hc X (Q X) M hXc hX hP (hq X hXq).2 hM
    (hb X hXb hXpos hQpos hPpos)
  dsimp only [M] at hminor0
  rw [Arithmetic597.minor_cutoff_identity (P := cutoff X (Q X)) (B := B) (δ := δ) hXpos hQpos (by linarith : 0 < Real.log X) rfl] at hminor0
  have hL11 : Real.log X ^ 11 ≤ Real.log X ^ 23 := pow_le_pow_right₀ hL (by norm_num)
  have hL23 : 1 ≤ Real.log X ^ 23 := one_le_pow₀ hL
  have hminor : (∑ m ∈ evenInterval X (4 * Q X ^ 2), ‖minorCoefficient X (Q X) m‖ ^ 2) ≤
      C * (4 * B + 1) * X ^ (2 + δ) * Real.log X ^ 23 := by
    calc
      _ ≤ C * (4 * B * X ^ (2 + δ) * Real.log X ^ 11 + X ^ (2 + δ)) := hminor0
      _ ≤ C * (4 * B * X ^ (2 + δ) * Real.log X ^ 23 + X ^ (2 + δ) * Real.log X ^ 23) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) hL23
      _ = _ := by ring
  have htail0 := hd X (4 * Q X ^ 2) (cutoff X (Q X)) (by linarith) hH hHX hP hPH
  have hscalar := Arithmetic597.tail_cutoff_scalar (X := X) hQpos hL hlogP0 hlogP (show cutoff X (Q X) = Q X / Real.log X ^ 10 from rfl)
  have hXpow : X ^ 2 ≤ X ^ (2 + δ) := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hXone (by linarith : (2 : ℝ) ≤ 2 + δ)
  have htail : (∑ m ∈ evenInterval X (4 * Q X ^ 2),
      ‖(representationCount X m : ℂ) * tail (cutoff X (Q X)) m‖ ^ 2) ≤
        5 * D * X ^ (2 + δ) * Real.log X ^ 23 := by
    calc
      _ ≤ D * X ^ 2 * (4 * Q X ^ 2 * Real.log (cutoff X (Q X)) ^ 3 /
          cutoff X (Q X) ^ 2 + Real.log X ^ 2) := htail0
      _ = D * (X ^ 2 * (4 * Q X ^ 2 * Real.log (cutoff X (Q X)) ^ 3 /
          cutoff X (Q X) ^ 2 + Real.log X ^ 2)) := by ring
      _ ≤ D * (5 * X ^ 2 * Real.log X ^ 23) := mul_le_mul_of_nonneg_left hscalar hD
      _ ≤ D * (5 * X ^ (2 + δ) * Real.log X ^ 23) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 2 * (∑ m ∈ evenInterval X (4 * Q X ^ 2), ‖minorCoefficient X (Q X) m‖ ^ 2) +
        2 * ∑ m ∈ evenInterval X (4 * Q X ^ 2),
          ‖(representationCount X m : ℂ) * tail (cutoff X (Q X)) m‖ ^ 2 := display13 X (Q X) _
    _ ≤ 2 * (C * (4 * B + 1) * X ^ (2 + δ) * Real.log X ^ 23) +
        2 * (5 * D * X ^ (2 + δ) * Real.log X ^ 23) := by gcongr
    _ = _ := by dsimp [K]; ring

/-- P0071 Theorem 2, with the original sealed statement, assembled from named cited leaves.
This is CONDITIONAL ON the arithmetic leaves, corrected GRH major arcs, corrected display 18,
and the standard prime power removal argument. It is not an unconditional proof of Theorem 2. -/
theorem theorem2_decomposed : Theorem2 := by
  intro hGRH ε0 hε0 Q hQ h5 ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨D, Xd, hD, hd⟩ := energy_bound hGRH hε0 Q hQ h5 hδ
  obtain ⟨B, Xb, hB, hb⟩ := corrected_major_arc hGRH
  obtain ⟨A, Xa, hA, ha⟩ := exceptional_energy_lower B hB
  obtain ⟨Xq, hq⟩ := hQ
  suffices ∀ᶠ X : ℝ in atTop, (EH X (4 * Q X ^ 2) : ℝ) ≤ (A * D) * X ^ ε by
    obtain ⟨X0, hX0⟩ := eventually_atTop.1 this
    exact ⟨A * D, X0, hX0⟩
  filter_upwards [eventual_cutoff hε0 Q ⟨Xq, hq⟩, eventually_ge_atTop Xd,
    eventually_ge_atTop Xb, eventually_ge_atTop Xa, eventually_ge_atTop Xq,
    Arithmetic597.eventually_log_pow_le_rpow 23 hδ] with X hgeom hXd hXb hXa hXq hLog
  rcases hgeom with ⟨hX, hL, hQpos, hP, hPQ, hQX, hlogP, hH, hHX, hPH⟩
  have hXpos : 0 < X := by linarith
  have hmajor := hb X (Q X) hXb hX hP (hq X hXq).2
  have hcount := ha X (4 * Q X ^ 2) hXa hX (by positivity) hHX (majorError X (Q X)) hmajor
  have hpow : X ^ (2 + δ) * X ^ δ = X ^ 2 * X ^ ε := by
    rw [← Real.rpow_add hXpos, show 2 + δ + δ = 2 + ε by dsimp [δ]; ring,
      Real.rpow_add hXpos]
    norm_num
  have hbound : (EH X (4 * Q X ^ 2) : ℝ) * X ^ 2 ≤ ((A * D) * X ^ ε) * X ^ 2 := by
    calc
      _ ≤ A * (∑ m ∈ evenInterval X (4 * Q X ^ 2),
          ‖fullCoefficient X m - mainTerm X m + majorError X (Q X) m‖ ^ 2) := hcount
      _ ≤ A * (D * X ^ (2 + δ) * Real.log X ^ 23) := mul_le_mul_of_nonneg_left (hd X hXd) hA
      _ ≤ A * (D * X ^ (2 + δ) * X ^ δ) := by gcongr
      _ = (A * D) * (X ^ (2 + δ) * X ^ δ) := by ring
      _ = _ := by rw [hpow]; ring
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < X ^ 2)).mp hbound

end LeanLab.LanguascoPerelli1996.Decomp597a
