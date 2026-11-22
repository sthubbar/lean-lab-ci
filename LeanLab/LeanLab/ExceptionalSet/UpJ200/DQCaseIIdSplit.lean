/-
ROUTE SPLIT, burst-20261122 unit P1122-0123, of the named hypothesis
`DQLeafNearZeroSelected.CaseIIdMajorLowerHyp`.
P0082, Bruedern and Perelli 1998, Ann. Inst. Fourier 48, pages 353 to 378,
https://doi.org/10.5802/aif.1621. Lemma 3 on page 358 with displays 12 and 13
on page 359, and Lemma 7 cases ii b to ii d on pages 363 and 364.

The paper's case ii d argument is
1. Lemma 3, display 20, for an even m sharing a factor with the exceptional
   modulus r, where the exceptional character vanishes at m and the middle
   error term of display 20 is zero, page 363 case ii b;
2. display 21 with an empty product: the modified singular series of
   display 12 is at most the singular series in size;
3. the bound I(m) at most m^beta for the sum of display 13, page 364;
4. the singular series lower bound S(m) >> m / phi(m) for even m, page 362
   case i, already proved in the lab as `singSeriesLowerHyp_proved672`;
5. elementary algebra: m - m^beta >> (1 - beta) m log P because
   (1 - beta) log P is at most a, and the exponential error of Lemma 3 is at
   most a quarter of the main term once delta is small.
Items 1 and 2 are LEAF theorems below. Items 3 and 5 are proved here, and the
exact statement `CaseIIdMajorLowerHyp` is assembled from them with no further
admitted step.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelectedDecisions
import LeanLab.ExceptionalSet.SingularSeriesLower672

namespace LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected (CaseIIdMajorLowerHyp)

/-- P0082 page 359 display 13: `I~(m) = Σ_{P < k < m - P} (k (m - k))^{β~ - 1}`.
The range is also cut to `0 < k < m`, which the condition `P < k < m - P`
already forces for every `P ≥ 0`, the only case the paper uses. -/
noncomputable def tildeI (β P : ℝ) (m : ℤ) : ℝ := by
  classical
  exact ∑ k ∈ (Finset.Ioo (0 : ℤ) m).filter
      (fun k : ℤ => P < (k : ℝ) ∧ (k : ℝ) < (m : ℝ) - P),
    ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1)

/-- P0082 page 359 display 12, the modified singular series
`S~(m) = χ~(-1) μ(r/(r,m)) r / (φ(r) φ(r/(r,m))) ∏_{p ∤ r m} (1 - 1/(p-1)^2)
∏_{p ∤ r, p ∣ m} (1 + 1/(p-1))`, for a character `χ~` of modulus `r`.
The value `χ~(-1)` is real, plus or minus one, for the real character of the
paper; its real part is taken so that the series is real valued. -/
noncomputable def tildeS {r : ℕ} (χ : DirichletCharacter ℂ r) (m : ℤ) : ℝ :=
  (χ (-1)).re * (ArithmeticFunction.moebius (r / Nat.gcd r m.natAbs) : ℝ) *
    ((r : ℝ) / ((r.totient : ℝ) * ((r / Nat.gcd r m.natAbs).totient : ℝ))) *
    ∏' p : Nat.Primes, (if (p : ℕ) ∣ r then 1 else
      if ((p : ℕ) : ℤ) ∣ m then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)

/-- LEAF: P0082 page 358 Lemma 3, display 20 on page 363, for even `m` with
`(m, r~) > 1`. HARD, a citation wall: Montgomery and Vaughan 1975 formula 6.17
with 6.19 kept explicit. `P = X^θ`, `θ = 6 δ`, page 357. The term with
`χ~(m)^2` is zero since `χ~(m) = 0`, page 363 case ii b. `X Γ₁ + X Γ₂` are
bounded by the envelopes of displays 14 and 15, `divisorError`, as in
`BPLemma3CoprimeHyp`. `P₀` is chosen after `θ`, as `δ` is fixed before `X`
grows on page 357. Constants may depend on `a`; see the notes. -/
theorem leaf_bp_lemma3_shared :
    ∀ a : ℝ, 0 < a → ∃ C c₂ : ℝ, 0 < C ∧ 0 < c₂ ∧
      ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
      ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
      ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
        χ.LFunction β = 0 →
        ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m → 1 < Int.gcd m r →
          |(R1 (X ^ θ) X m).re - ((m : ℝ) * singSeries m + tildeI β (X ^ θ) m * tildeS χ m)| ≤
            C * X * divisorError r (X ^ θ) m +
            C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
              Real.exp (-(c₂ / θ)) * Real.log (X ^ θ) := by
  sorry

/-- LEAF: P0082 page 363 display 21, citing Montgomery and Vaughan 1975 (8.5),
in the case of case ii c and ii d where the product of display 21 is empty:
every prime `p > 3` dividing `r` divides `m`. Then `|S~(m)| ≤ S(m)` for even
`m`. MEDIUM: a comparison of the Euler factors of displays 11 and 12, one prime
at a time; at a prime `p ∣ r` with `p ∤ m` the ratio is `1/(p-2)`, which is one
for `p = 3`, and at a prime `p ∣ r` with `p ∣ m` it is one or `1/(p-1)`. -/
theorem leaf_tildeS_le_of_empty (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (m : ℤ) (hm : 1 ≤ m) (he : Even m)
    (hprod : ¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) :
    |tildeS χ m| ≤ singSeries m := by
  sorry

/-- P0082 page 364 case ii d, `I~(m) ≤ m^β~`, together with `I~(m) ≥ 0`.
Each `k` in the range has `k (m - k) ≥ m - 1`, so each term is at most
`(m - 1)^{β - 1}` and there are at most `m - 1` terms. Proved. -/
theorem tildeI_bounds (β P : ℝ) (m : ℤ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hm : 1 ≤ m) :
    0 ≤ tildeI β P m ∧ tildeI β P m ≤ (m : ℝ) ^ β := by
  classical
  unfold tildeI
  set s := (Finset.Ioo (0 : ℤ) m).filter
      (fun k : ℤ => P < (k : ℝ) ∧ (k : ℝ) < (m : ℝ) - P) with hs
  have hmem : ∀ k ∈ s, 1 ≤ k ∧ k ≤ m - 1 := by
    intro k hk
    have := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hk).1)
    omega
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    obtain ⟨h1, h2⟩ := hmem k hk
    have : (0 : ℝ) ≤ (k : ℝ) * ((m : ℝ) - k) := by
      have a1 : (1 : ℝ) ≤ k := by exact_mod_cast h1
      have a2 : (k : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast h2
      nlinarith
    exact Real.rpow_nonneg this _
  · rcases eq_or_lt_of_le hm with h | h
    · subst h
      have : s = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk; have := hmem k hk; omega
      rw [this, Finset.sum_empty]; simp
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast h
    have hpos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have hterm : ∀ k ∈ s, ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1) ≤ ((m : ℝ) - 1) ^ (β - 1) := by
      intro k hk
      obtain ⟨h1, h2⟩ := hmem k hk
      have a1 : (1 : ℝ) ≤ k := by exact_mod_cast h1
      have a2 : (k : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast h2
      apply Real.rpow_le_rpow_of_nonpos hpos _ (by linarith)
      nlinarith
    have hcard : (s.card : ℝ) ≤ (m : ℝ) - 1 := by
      have hc : s.card ≤ (Finset.Ioo (0 : ℤ) m).card := Finset.card_filter_le _ _
      rw [Int.card_Ioo] at hc
      have : ((m - 0).toNat : ℤ) = m := by
        rw [sub_zero]; exact Int.toNat_of_nonneg (by omega)
      have hc' : (s.card : ℤ) ≤ m - 1 := by
        have : ((s.card : ℕ) : ℤ) ≤ ((m - 0 - 1).toNat : ℤ) := by exact_mod_cast hc
        rw [Int.toNat_of_nonneg (by omega)] at this; simpa using this
      have : ((s.card : ℤ) : ℝ) ≤ ((m - 1 : ℤ) : ℝ) := by exact_mod_cast hc'
      push_cast at this; exact this
    calc ∑ k ∈ s, ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1)
        ≤ ∑ _k ∈ s, ((m : ℝ) - 1) ^ (β - 1) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * ((m : ℝ) - 1) ^ (β - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((m : ℝ) - 1) * ((m : ℝ) - 1) ^ (β - 1) :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hpos.le _)
      _ = ((m : ℝ) - 1) ^ β := by
          rw [← Real.rpow_one_add' hpos.le (by linarith)]; ring_nf
      _ ≤ (m : ℝ) ^ β := Real.rpow_le_rpow hpos.le (by linarith) hβ0.le

/-- P0082 page 364 case ii d, first display: with `|S~| ≤ S` and
`0 ≤ I~ ≤ m^β`, `m S + I~ S~ ≥ S (m - m^β)`. Proved. -/
theorem main_term_lower (m S I St mb : ℝ) (hS : 0 ≤ S) (hI0 : 0 ≤ I) (hI : I ≤ mb)
    (hSt : |St| ≤ S) : S * (m - mb) ≤ m * S + I * St := by
  have h1 : -(I * S) ≤ I * St := by
    have := (abs_le.mp hSt).1
    nlinarith
  have h2 : I * S ≤ mb * S := mul_le_mul_of_nonneg_right hI hS
  nlinarith

/-- P0082 page 364 case ii d, `m - m^β >> (1 - β) m log P`: with
`y = (1 - β) log P ≤ a` and `log P ≤ log m`, one has
`m - m^β ≥ e^{-a} y m`. Proved. -/
theorem gap_lower (m β L a : ℝ) (hm : 0 < m) (hL : 0 < L) (hLm : L ≤ Real.log m)
    (hβ1 : β < 1) (hβa : (1 - β) * L ≤ a) :
    m * ((1 - β) * L) * Real.exp (-a) ≤ m - m ^ β := by
  set y := (1 - β) * L with hy
  have hy0 : 0 ≤ y := by have : 0 < 1 - β := by linarith
                         positivity
  have hmb : m ^ β = m * Real.exp (-((1 - β) * Real.log m)) := by
    calc m ^ β = Real.exp (Real.log m * β) := Real.rpow_def_of_pos hm _
      _ = Real.exp (Real.log m) * Real.exp (-((1 - β) * Real.log m)) := by
          rw [← Real.exp_add]; congr 1; ring
      _ = m * Real.exp (-((1 - β) * Real.log m)) := by rw [Real.exp_log hm]
  have hle : Real.exp (-((1 - β) * Real.log m)) ≤ Real.exp (-y) := by
    apply Real.exp_le_exp.mpr
    have : y ≤ (1 - β) * Real.log m :=
      mul_le_mul_of_nonneg_left hLm (by linarith)
    linarith
  have hexp : y * Real.exp (-a) ≤ 1 - Real.exp (-y) := by
    have h1 := Real.add_one_le_exp y
    have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (-a) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    have h4 : 0 < Real.exp (-y) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left h1 h4.le, mul_le_mul_of_nonneg_left h3 hy0]
  rw [hmb]
  have : m * Real.exp (-((1 - β) * Real.log m)) ≤ m * Real.exp (-y) :=
    mul_le_mul_of_nonneg_left hle hm.le
  nlinarith [mul_le_mul_of_nonneg_left hexp hm.le]

/-- P0082 page 364 case ii d, the closing comparison: the exponential error of
Lemma 3 is at most a quarter of the main term once delta is small. Proved. -/
theorem combine_ii_d (R T D CE c₀ ea M X y : ℝ)
    (hR : T - D - CE * X * M * y ≤ R) (hT : c₀ * ea * M * y * X / 2 ≤ T)
    (hCE : CE ≤ c₀ * ea / 4) (hM : 1 ≤ M) (hX : 0 ≤ X) (hy : 0 ≤ y)
    (hc₀ : 0 < c₀) (hea : 0 < ea) :
    c₀ * ea / 4 * y * X ≤ R + D := by
  have hXMy : 0 ≤ X * M * y := by positivity
  have h1 : CE * (X * M * y) ≤ c₀ * ea / 4 * (X * M * y) :=
    mul_le_mul_of_nonneg_right hCE hXMy
  have h2 : c₀ * ea / 4 * y * X * 1 ≤ c₀ * ea / 4 * y * X * M :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  nlinarith

/-- P0082 page 364 case ii d. The exact named hypothesis
`DQLeafNearZeroSelected.CaseIIdMajorLowerHyp`, from the two LEAF theorems
`leaf_bp_lemma3_shared` and `leaf_tildeS_le_of_empty`, the proved
`tildeI_bounds` and the proved singular series bound
`Task672.singSeriesLowerHyp_proved672`. -/
theorem caseIIdMajorLowerHyp_of_leaves : CaseIIdMajorLowerHyp := by
  intro γ h1 h2 a ha
  obtain ⟨C, c₂, hC, hc₂, hL3θ⟩ := leaf_bp_lemma3_shared a ha
  obtain ⟨c₀, hc₀, hS⟩ := LeanLab.ExceptionalSet.Task672.singSeriesLowerHyp_proved672
  set K : ℝ := 4 * C * Real.exp a / c₀ with hK
  have hKpos : 0 < K := by positivity
  refine ⟨min (1 / 100) (c₂ / (6 * (|Real.log K| + 1))), lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδlt
  have hδ1 : δ < 1 / 100 := (lt_min_iff.mp hδlt).1
  have hδ2 : δ < c₂ / (6 * (|Real.log K| + 1)) := (lt_min_iff.mp hδlt).2
  have hθ : (6 * δ : ℝ) < 6 / 100 := by linarith
  obtain ⟨P₀, hL3⟩ := hL3θ (6 * δ) (by positivity) hθ
  refine ⟨c₀ * Real.exp (-a) / 4, C, by positivity, hC, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  have hQ : Tendsto (fun N : ℕ => F γ N ^ (1 - 6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - 6 * δ)).comp hF
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hP.eventually_ge_atTop (max P₀ 2)).and (hQ.eventually_ge_atTop 2))
  refine ⟨N₀, ?_⟩
  intro N hN r hr hrP hsel m hev hlow hle hgcd hprod hrz χ β hp hreal hne hβ0 hβlo hβ1 hz
  obtain ⟨hPN, hQN⟩ := hN₀ N hN
  have hX : 0 < F γ N := Real.exp_pos _
  have hP2 : 2 ≤ F γ N ^ (6 * δ) := le_trans (le_max_right _ _) hPN
  have hPP₀ : P₀ ≤ F γ N ^ (6 * δ) := le_trans (le_max_left _ _) hPN
  have hsplit : F γ N = F γ N ^ (6 * δ) * F γ N ^ (1 - 6 * δ) := by
    rw [← Real.rpow_add hX]; simp
  have hPX : F γ N ^ (6 * δ) ≤ F γ N / 2 := by
    have hPpos : 0 ≤ F γ N ^ (6 * δ) := by linarith
    have := mul_le_mul_of_nonneg_left hQN hPpos
    rw [← hsplit] at this; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hm1 : 1 ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hmpos
    omega
  have hr1 : r ≠ 1 := by
    rintro rfl; simp at hgcd
  have hbound := hL3 (F γ N) hX hPP₀ r hr hr1 hrP hsel hrz χ β hp
    hreal hne hβlo hβ1 hz m hm1 hle hev hgcd
  have := hrz
  set X := F γ N with hXdef
  set P := X ^ (6 * δ) with hPdef
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  have hmnat : 1 ≤ m.toNat := by omega
  have hφpos : (0 : ℝ) < (m.toNat.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM : 1 ≤ M := by
    rw [hMdef, le_div_iff₀ hφpos, one_mul]; exact_mod_cast Nat.totient_le _
  have hSm : c₀ * M ≤ singSeries m := hS m hm1 hev
  have hS0 : 0 ≤ singSeries m := le_trans (by positivity) hSm
  have hSt := leaf_tildeS_le_of_empty r χ m hm1 hev hprod
  obtain ⟨hI0, hI⟩ := tildeI_bounds β P m hβ0 hβ1.le hm1
  have hL : 0 < Real.log P := Real.log_pos (by linarith)
  have hLm : Real.log P ≤ Real.log m := Real.log_le_log (by linarith) (by linarith)
  have hβa : (1 - β) * Real.log P ≤ a := by
    have h' : 1 - β ≤ a / Real.log P := by linarith
    calc (1 - β) * Real.log P ≤ a / Real.log P * Real.log P :=
          mul_le_mul_of_nonneg_right h' hL.le
      _ = a := div_mul_cancel₀ a hL.ne'
  have hgap := gap_lower m β (Real.log P) a hmpos hL hLm hβ1 hβa
  have hmain := main_term_lower m (singSeries m) (tildeI β P m) (tildeS χ m) ((m : ℝ) ^ β)
    hS0 hI0 hI hSt
  set y := (1 - β) * Real.log P with hydef
  have hy0 : 0 ≤ y := by
    have : 0 < 1 - β := by linarith
    positivity
  have hea : 0 < Real.exp (-a) := Real.exp_pos _
  have hT : c₀ * Real.exp (-a) * M * y * X / 2 ≤
      (m : ℝ) * singSeries m + tildeI β P m * tildeS χ m := by
    have e1 : singSeries m * ((m : ℝ) * y * Real.exp (-a)) ≤ singSeries m * ((m : ℝ) - (m : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left hgap hS0
    have e2 : c₀ * M * ((m : ℝ) * y * Real.exp (-a)) ≤ singSeries m * ((m : ℝ) * y * Real.exp (-a)) :=
      mul_le_mul_of_nonneg_right hSm (by positivity)
    have e3 : c₀ * M * (X / 2 * y * Real.exp (-a)) ≤ c₀ * M * ((m : ℝ) * y * Real.exp (-a)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlow.le hy0) hea.le
    have e4 : c₀ * Real.exp (-a) * M * y * X / 2 = c₀ * M * (X / 2 * y * Real.exp (-a)) := by ring
    linarith
  have hR := (abs_le.mp hbound).1
  have hcmp : |Real.log K| + 1 < c₂ / (6 * δ) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hδ2
    linarith
  have hexpK : Real.exp (-(c₂ / (6 * δ))) ≤ K⁻¹ := by
    rw [← Real.exp_log hKpos, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have := le_abs_self (Real.log K)
    linarith
  have hCE : C * Real.exp (-(c₂ / (6 * δ))) ≤ c₀ * Real.exp (-a) / 4 := by
    have hKinv : C * K⁻¹ = c₀ * Real.exp (-a) / 4 := by
      rw [hK, Real.exp_neg]
      field_simp
    calc C * Real.exp (-(c₂ / (6 * δ))) ≤ C * K⁻¹ := mul_le_mul_of_nonneg_left hexpK hC.le
      _ = _ := hKinv
  have hR' : (m : ℝ) * singSeries m + tildeI β P m * tildeS χ m - C * X * divisorError r P m -
      C * Real.exp (-(c₂ / (6 * δ))) * X * M * y ≤ (R1 P X m).re := by
    have e : C * X * M * (1 - β) * Real.exp (-(c₂ / (6 * δ))) * Real.log P =
        C * Real.exp (-(c₂ / (6 * δ))) * X * M * y := by rw [hydef]; ring
    linarith
  have hfin := combine_ii_d (R1 P X m).re ((m : ℝ) * singSeries m + tildeI β P m * tildeS χ m)
    (C * X * divisorError r P m) (C * Real.exp (-(c₂ / (6 * δ)))) c₀ (Real.exp (-a)) M X y
    hR' hT hCE hM hX.le hy0 hc₀ hea
  have e : c₀ * Real.exp (-a) / 4 * (1 - β) * Real.log P * X =
      c₀ * Real.exp (-a) / 4 * y * X := by rw [hydef]; ring
  linarith

end LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit.tildeI_bounds
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit.main_term_lower
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit.gap_lower
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit.combine_ii_d
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit.caseIIdMajorLowerHyp_of_leaves
