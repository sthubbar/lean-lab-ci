/-
ENCODING A of P0089 Languasco 2004, moved here 2026-10-28 by the architect with Steve live. It was
the PC copy of Languasco2004/Statements.lean, 518 lines, built on the PC against encoding A of
Perelli 1996, and never reached main, which kept its own 88 line Statements.lean. Verbatim except
the namespace, now `LeanLab.Languasco2004.EncA`, and the Perelli import and opens, now
Perelli1996.StatementsA and `LeanLab.Perelli1996.EncA`.
-/
/-
P0089 A. Languasco, The exceptional set in short intervals for two additive problems with
primes: a survey, Riv. Mat. Univ. Parma (7) 3* (2004), 223-231.
The text layer garbles every exponent of `H`; Theorems 1.5 to 1.8, 2.2 to 2.4, the outline
parameters and p. 224 were read on page images at 300 dpi.

Each quoted result is attributed to the original paper the survey cites:
* Theorem 1.1, Montgomery-Vaughan [15]: the lab's `ExceptionalSet.montgomeryVaughan`.
* Li [12] 1999, `δ = 0.079`, CITED; Pintz [21] announced `δ = 1/3`, a def, not a theorem.
* Theorem 1.5, Jia [8]; 1.6, Perelli-Pintz [18]; 1.7, Luo-Yao [13] and Yao [26];
  1.8, Languasco [10]; 2.1, Brünner-Perelli-Pintz [2], also A. I. Vinogradov [24];
  Zaccagnini [27]; 2.2, Perelli-Pintz [19] and Mikawa [14]; 2.3, Perelli-Zaccagnini [20];
  2.4, Languasco [11]: CITED, sorry.
* PROVED: monotonicity of the ranges in `H` and in the exponents, the reparametrisation of
  `∃ δ` statements, power saving implies log saving, a short interval power saving at `H = X`
  gives the lab's `PowerSaving`, Theorem 1.6 from Perelli 1996's `7/(36k)` remark at `k = 1`,
  2.3 at `k = 2` is 2.2, and the outline exponent arithmetic.
* QUESTION, PRELIMINARY: the outline parameters of Theorems 1.8 and 2.4 give a narrower
  range than the theorems state, see STATEMENTS.md.

AI-written Lean code, Claude, 2026-10-18, run 20261018T1603Z-12862.
Checked only by the Lean kernel. Binary Goldbach and the Hardy-Littlewood conjectures are OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.ExceptionalSet.Statements
import LeanLab.LanguascoPerelli1996.Statements
import LeanLab.Perelli1996.StatementsA

namespace LeanLab.Languasco2004.EncA
open Real Filter Topology Polynomial
open LeanLab.LanguascoPerelli1996 (EH)

attribute [local instance] Classical.propDecidable

/-! ### Shapes of short interval bounds, for any count `cnt X H` -/

/-- A count on `[X, X+H]`. -/
abbrev Count := ℝ → ℝ → ℕ

/-- `cnt(X,H) ≪ H^{1-s}` uniformly for `X^r ≤ H ≤ X`. -/
def PS (cnt : Count) (r s : ℝ) : Prop :=
  ∃ C X0 : ℝ, ∀ X H : ℝ, X0 ≤ X → X ^ r ≤ H → H ≤ X → (cnt X H : ℝ) ≤ C * H ^ (1 - s)

/-- The survey's shape "there is an effectively computable `δ > 0` such that for
`H ≥ X^{θ+cδ}`, `cnt ≪ H^{1-δ/m}`". The range is read as non empty, `θ + cδ < 1`, the surveyed
setting `H = o(X)`; without it a large `δ` would make the statement empty. -/
def PSdelta (cnt : Count) (θ c m : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ θ + c * δ < 1 ∧ PS cnt (θ + c * δ) (δ / m)

/-- `cnt(X,H) ≪_A H log^{-A} X` uniformly for `X^r ≤ H ≤ X`. -/
def LogFrom (cnt : Count) (r : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X H : ℝ, X0 ≤ X → X ^ r ≤ H → H ≤ X →
    (cnt X H : ℝ) ≤ C * H / Real.log X ^ A

/-- For every `ε > 0`, `LogFrom cnt (θ + ε)`. -/
def ShortLog (cnt : Count) (θ : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → LogFrom cnt (θ + ε)

/-- The same for `0 < ε < e1` only. -/
def ShortLogBelow (cnt : Count) (θ e1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < e1 → LogFrom cnt (θ + ε)

/-! ### Section 1, Goldbach, p. 223-227. `E(X,H) = E ∩ [X, X+H]` is `LanguascoPerelli1996.EH`. -/

/-- Theorem 1.1, Montgomery-Vaughan [15], p. 223, is the lab's cited statement. -/
theorem theorem1_1 : LeanLab.ExceptionalSet.PowerSaving := LeanLab.ExceptionalSet.montgomeryVaughan

/-- Li [12], Quart. J. Math. Oxford 50, 1999: `δ = 0.079`, p. 224. -/
def Li1999 : Prop := LeanLab.ExceptionalSet.PowerBound (1 - 0.079)

/-- CITED. Li 1999, as quoted p. 224. -/
theorem li1999 : Li1999 := by sorry

/-- Pintz [21] announced `δ = 1/3`, p. 224; an announcement, kept as a def. -/
def PintzAnnounced : Prop := LeanLab.ExceptionalSet.PowerBound (2 / 3)

/-- **Theorem 1.5**, Jia [8], Acta Arith. 77, 1996, p. 225: `H ≥ X^{7/108+ε}`. -/
def Theorem1_5 : Prop := ShortLog EH (7 / 108)

/-- CITED. Jia 1996. -/
theorem jia : Theorem1_5 := by sorry

/-- **Theorem 1.6**, Perelli-Pintz [18], J. London Math. Soc. 47, 1993, p. 225:
`0 < ε < 5/6`, `H ≥ X^{7/36+ε}`. -/
def Theorem1_6 : Prop := ShortLogBelow EH (7 / 36) (5 / 6)

/-- CITED. Perelli-Pintz 1993. -/
theorem perelliPintz1993 : Theorem1_6 := by sorry

/-- **Theorem 1.7**, Luo-Yao [13] and Yao [26], corrected, p. 226: `H ≥ X^{7/12+2δ}`,
`≪ H^{1-δ}`. -/
def Theorem1_7 : Prop := PSdelta EH (7 / 12) 2 1

/-- CITED. Luo-Yao 1981 and Yao 1982, in the corrected form of p. 226. -/
theorem luoYao : Theorem1_7 := by sorry

/-- The uncorrected Luo-Yao statement, p. 225: `H ≥ X^{7/12+ε}` for every `ε`, `≪ H^{1-δ}`.
The survey says the proof has an oversight; a def only. -/
def LuoYaoClaimed : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → PS EH (7 / 12 + ε) δ

/-- Peneva [16], [17], p. 226: the same estimate for `H ≥ X^{1/3+δ}`. -/
def Peneva : Prop := PSdelta EH (1 / 3) 1 1

/-- CITED. Peneva 2001 with the Corrigendum 2004. -/
theorem peneva : Peneva := by sorry

/-- Peneva's stated range `H > X^{1/3}`, p. 226, "not reached by her proof"; a def only. -/
def PenevaClaimed : Prop := ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ PS EH (1 / 3) δ

/-- **Theorem 1.8**, Languasco [10], Monatsh. Math. 141, 2004, p. 226: `H ≥ X^{7/24+7δ}`,
`≪ H^{1-δ/600}`. -/
def Theorem1_8 : Prop := PSdelta EH (7 / 24) 7 600

/-- CITED. Languasco 2004, Monatsh. Math. -/
theorem languasco2004a : Theorem1_8 := by sorry

/-- The open problem of p. 227: the estimate of Theorem 1.8 for `H ≥ X^{7/36+δ}`; read with
the same saving `δ/600`. A def. -/
def OpenProblem1 : Prop := PSdelta EH (7 / 36) 1 600

/-! ### Section 2, Hardy-Littlewood, p. 227-230 -/

/-- `n` is an HL-number: `n = p + m^k`, `p` prime, `m ≥ 1`. -/
def IsHL (k n : ℕ) : Prop := ∃ p m : ℕ, p.Prime ∧ 1 ≤ m ∧ p + m ^ k = n

/-- `n` is a `k`-th power. -/
def IsPow (k n : ℕ) : Prop := ∃ m : ℕ, m ^ k = n

/-- `E_k(X) = E_k ∩ [1, X]`. -/
noncomputable def Ek (k X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n : ℕ => ¬ IsHL k n ∧ ¬ IsPow k n)).card

/-- `E_k(X,H) = E_k ∩ [X, X+H]`. -/
noncomputable def EkH (k : ℕ) (X H : ℝ) : ℕ :=
  ((Finset.Icc ⌈X⌉₊ ⌊X + H⌋₊).filter (fun n : ℕ => ¬ IsHL k n ∧ ¬ IsPow k n)).card

/-- The Hardy-Littlewood conjectures, p. 227, `k = 2, 3`, OPEN: `abs E_k(X) ≪ 1`. -/
def HLConjecture (k : ℕ) : Prop := ∃ C : ℝ, ∀ X : ℕ, (Ek k X : ℝ) ≤ C

/-- `abs E_k(X) ≪ X^{1-δ}` for some `δ > 0`. -/
def HLPowerSaving (k : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → (Ek k X : ℝ) ≤ C * (X : ℝ) ^ (1 - δ)

/-- **Theorem 2.1**, Brünner-Perelli-Pintz [2], Acta Math. Hungar. 53, 1989, p. 228. CITED;
A. I. Vinogradov [24] proved the same. -/
theorem brunnerPerelliPintz : HLPowerSaving 2 := by sorry

/-- Zaccagnini [27], Mathematika 39, 1992, p. 228: the same for every `k ≥ 2`. CITED. -/
theorem zaccagnini : ∀ k : ℕ, 2 ≤ k → HLPowerSaving k := by sorry

/-- **Theorem 2.2**, Perelli-Pintz [19], J. Number Theory 54, 1995, and Mikawa [14], p. 228:
`H ≥ X^{7/24+ε}`. -/
def Theorem2_2 : Prop := ShortLog (EkH 2) (7 / 24)

/-- CITED. Perelli-Pintz 1995, Mikawa 1993. -/
theorem perelliPintzMikawa : Theorem2_2 := by sorry

/-- **Theorem 2.3**, Perelli-Zaccagnini [20], Izv. Math. 59, 1995, p. 228:
`H ≥ X^{7/12(1-1/k)+ε}`. -/
def Theorem2_3 : Prop := ∀ k : ℕ, 2 ≤ k → ShortLog (EkH k) (7 / 12 * (1 - 1 / (k : ℝ)))

/-- CITED. Perelli-Zaccagnini 1995. -/
theorem perelliZaccagnini : Theorem2_3 := by sorry

/-- **Theorem 2.4**, Languasco [11], Tsukuba J. Math. 28, 2004, p. 229: `K = 2^{k-2}`,
`H ≥ X^{7/12(1-1/k)+δ}`, `≪ H^{1-δ/(5K)}`. -/
def Theorem2_4 : Prop :=
  ∀ k : ℕ, 2 ≤ k → PSdelta (EkH k) (7 / 12 * (1 - 1 / (k : ℝ))) 1 (5 * 2 ^ (k - 2))

/-- CITED. Languasco 2004, Tsukuba. -/
theorem languasco2004b : Theorem2_4 := by sorry

/-- The question of p. 230: under GRH, `abs E_k(X,H) ≪ H^{1-1/(ck)}`, `c` absolute, for
`H ≫ X^{(1/2)(1-1/k)+ε}`. A def. -/
def GRHQuestion : Prop :=
  LeanLab.DERZ1997.GRH → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε →
    PS (EkH k) (1 / 2 * (1 - 1 / (k : ℝ)) + ε) (1 / (c * k))

/-! ### PROVED: monotonicity and reparametrisation -/

theorem EH_mono {X H H' : ℝ} (h : H ≤ H') : EH X H ≤ EH X H' := by
  unfold EH
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor (by linarith))⟩, hn.2⟩

theorem EkH_mono {k : ℕ} {X H H' : ℝ} (h : H ≤ H') : EkH k X H ≤ EkH k X H' := by
  unfold EkH
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor (by linarith))⟩, hn.2⟩

/-- A log saving from `X^r` gives one from any `X^{r'}`, `r ≤ r'`. -/
theorem LogFrom_mono {cnt : Count} {r r' : ℝ} (hr : r ≤ r') (h : LogFrom cnt r) :
    LogFrom cnt r' := by
  intro A hA
  obtain ⟨C, X0, hC⟩ := h A hA
  refine ⟨C, max X0 1, fun X H hX h1 h2 => hC X H (le_trans (le_max_left _ _) hX) ?_ h2⟩
  exact le_trans (Real.rpow_le_rpow_of_exponent_le (le_trans (le_max_right _ _) hX) hr) h1

theorem ShortLog_mono {cnt : Count} {θ θ' : ℝ} (hθ : θ ≤ θ') (h : ShortLog cnt θ) :
    ShortLog cnt θ' := fun ε hε => LogFrom_mono (by linarith) (h ε hε)

/-- When `θ + e1 > 1` the restriction `ε < e1` is void: the range `X^{θ+ε} ≤ H ≤ X` is empty
for `X > 1`. -/
theorem shortLog_of_below {cnt : Count} {θ e1 : ℝ} (he : 1 < θ + e1)
    (h : ShortLogBelow cnt θ e1) : ShortLog cnt θ := by
  intro ε hε
  by_cases hlt : ε < e1
  · exact h ε hε hlt
  · intro A _
    refine ⟨0, 2, fun X H hX h1 h2 => ?_⟩
    exfalso
    have hX1 : 1 < X := by linarith
    have : X ^ (1 : ℝ) < X ^ (θ + ε) := Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith)
    rw [Real.rpow_one] at this
    linarith

/-- A power saving range can be narrowed and the saving weakened. -/
theorem PS_mono {cnt : Count} {r r' s s' : ℝ} (hr0 : 0 ≤ r') (hr : r ≤ r') (hs : s' ≤ s)
    (h : PS cnt r s) : PS cnt r' s' := by
  obtain ⟨C, X0, hC⟩ := h
  refine ⟨max C 0, max X0 1, fun X H hX h1 h2 => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hH1 : 1 ≤ H := le_trans (Real.one_le_rpow hX1 hr0) h1
  have h1' : X ^ r ≤ H := le_trans (Real.rpow_le_rpow_of_exponent_le hX1 hr) h1
  calc (cnt X H : ℝ) ≤ C * H ^ (1 - s) := hC X H (le_trans (le_max_left _ _) hX) h1' h2
    _ ≤ max C 0 * H ^ (1 - s) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * H ^ (1 - s') :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
          (le_max_right _ _)

/-- Reparametrising `∃ δ`: `(θ, c, m)` gives `(θ, c', m')` when `c m ≤ c' m'`. -/
theorem PSdelta_reparam {cnt : Count} {θ c m c' m' : ℝ} (hθ : 0 ≤ θ) (hc : 0 < c)
    (hc' : 0 < c') (hm : 0 < m) (hm' : 0 < m') (hcm : c * m ≤ c' * m')
    (h : PSdelta cnt θ c m) : PSdelta cnt θ c' m' := by
  obtain ⟨δ, hδ, hlt, hP⟩ := h
  refine ⟨c * δ / c', by positivity, ?_, ?_⟩
  · have : c' * (c * δ / c') = c * δ := by field_simp
    rw [this]; exact hlt
  · have e : θ + c' * (c * δ / c') = θ + c * δ := by field_simp
    rw [e]
    refine PS_mono (by positivity) le_rfl ?_ hP
    rw [div_div, div_le_div_iff₀ (by positivity) hm]
    have := mul_le_mul_of_nonneg_left hcm hδ.le
    nlinarith

/-- A power saving for `H ≥ X^r`, `r, s > 0`, gives the log saving from `X^r`. -/
theorem logFrom_of_PS {cnt : Count} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (h : PS cnt r s) :
    LogFrom cnt r := by
  intro A hA
  obtain ⟨C, X0, hC⟩ := h
  have hb := (isLittleO_log_rpow_rpow_atTop A (mul_pos hr hs)).bound one_pos
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max C 0, max (max X0 X1) 2, fun X H hX h1 h2 => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hlA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlog A
  have hXr : 0 < X ^ r := Real.rpow_pos_of_pos hXpos r
  have hHpos : 0 < H := lt_of_lt_of_le hXr h1
  have hbX := hX1 X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
  rw [Real.norm_of_nonneg hlA.le, Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le _),
    one_mul] at hbX
  have hc := hC X H (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX) h1 h2
  have hsplit : H ^ (1 - s) = H * H ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add hHpos, Real.rpow_one]
  have hHs : H ^ (-s) ≤ (X ^ r) ^ (-s) := Real.rpow_le_rpow_of_nonpos hXr h1 (by linarith)
  have hXrs : (X ^ r) ^ (-s) = (X ^ (r * s))⁻¹ := by
    rw [← Real.rpow_mul hXpos.le, show r * -s = -(r * s) by ring, Real.rpow_neg hXpos.le]
  have hinv : (X ^ (r * s))⁻¹ ≤ 1 / Real.log X ^ A := by
    rw [one_div]; exact inv_anti₀ hlA hbX
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (cnt X H : ℝ) ≤ C * H ^ (1 - s) := hc
    _ ≤ max C 0 * H ^ (1 - s) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hHpos.le _)
    _ = max C 0 * H * H ^ (-s) := by rw [hsplit]; ring
    _ ≤ max C 0 * H * (1 / Real.log X ^ A) := by
        apply mul_le_mul_of_nonneg_left (hHs.trans (hXrs ▸ hinv)) (by positivity)
    _ = max C 0 * H / Real.log X ^ A := by ring

/-- A short interval power saving of the survey's shape gives the lab's `PowerSaving`,
Montgomery-Vaughan's Theorem 1.1, by taking `H = X`. -/
theorem powerSaving_of_PSdelta {θ c m : ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hm : 0 < m)
    (h : PSdelta EH θ c m) : LeanLab.ExceptionalSet.PowerSaving := by
  obtain ⟨δ, hδ, hlt, hP⟩ := h
  set s' := min (δ / m) (1 / 2) with hs'
  have hs'pos : 0 < s' := lt_min (by positivity) (by norm_num)
  have hs'le : s' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C, X0, hC⟩ := PS_mono (by positivity) le_rfl (min_le_left _ _) hP
  refine ⟨s', hs'pos, LeanLab.LanguascoPerelli1996.powerBound_of_dyadic (X0 := max X0 1)
    (C := C) (by linarith) (fun X hX => ?_)⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hr : X ^ (θ + c * δ) ≤ X := by
    calc X ^ (θ + c * δ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hlt.le
      _ = X := Real.rpow_one X
  exact hC X X (le_trans (le_max_left _ _) hX) hr le_rfl

/-! ### PROVED: implications between the quoted results -/

/-- Jia's range is wider than Perelli-Pintz's: Theorem 1.5 implies Theorem 1.6. -/
theorem theorem1_6_of_theorem1_5 (h : Theorem1_5) : Theorem1_6 :=
  fun ε hε _ => ShortLog_mono (θ := 7 / 108) (θ' := 7 / 36) (by norm_num) h ε hε

/-- Theorem 1.6 holds for every `ε > 0`, since `7/36 + 5/6 > 1`. -/
theorem theorem1_6_all (h : Theorem1_6) : ShortLog EH (7 / 36) :=
  shortLog_of_below (by norm_num) h

/-- Theorem 1.8, 1.7 and Peneva each give Montgomery-Vaughan's Theorem 1.1. -/
theorem theorem1_1_of_theorem1_8 (h : Theorem1_8) : LeanLab.ExceptionalSet.PowerSaving :=
  powerSaving_of_PSdelta (by norm_num) (by norm_num) (by norm_num) h

theorem theorem1_1_of_theorem1_7 (h : Theorem1_7) : LeanLab.ExceptionalSet.PowerSaving :=
  powerSaving_of_PSdelta (by norm_num) (by norm_num) (by norm_num) h

theorem theorem1_1_of_peneva (h : Peneva) : LeanLab.ExceptionalSet.PowerSaving :=
  powerSaving_of_PSdelta (by norm_num) (by norm_num) (by norm_num) h

/-- Theorem 1.8 from the lab's cited Languasco statement, through `H = X`. -/
theorem montgomeryVaughan_via_languasco : LeanLab.ExceptionalSet.PowerSaving :=
  theorem1_1_of_theorem1_8 languasco2004a

/-- The open problem in its `c = 1` form gives the `c = 7` form at the same base `7/36`, the
shape of Theorem 1.8, since `1 · 600 ≤ 7 · 600`. -/
theorem openProblem_reparam (h : OpenProblem1) : PSdelta EH (7 / 36) 7 600 :=
  PSdelta_reparam (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h

/-- Li 1999, `δ = 0.079`, follows from the lab's Li 2000, `δ = 0.086`. -/
theorem li1999_of_li2000 (h : LeanLab.ExceptionalSet.PowerBound 0.914) : Li1999 :=
  LeanLab.ExceptionalSet.powerBound_mono (by norm_num) h

/-- Pintz's announced `X^{2/3}` would give Zhao's `X^{7/10}` and the whole lab chain. -/
theorem zhao_of_pintzAnnounced (h : PintzAnnounced) : LeanLab.ExceptionalSet.PowerBound (7 / 10) :=
  LeanLab.ExceptionalSet.powerBound_mono (by norm_num) h

/-- Theorem 2.3 at `k = 2` is Theorem 2.2. -/
theorem theorem2_2_of_theorem2_3 (h : Theorem2_3) : Theorem2_2 := by
  have := h 2 le_rfl
  norm_num at this ⊢
  exact this

/-- Theorem 2.4 gives a log saving of Perelli-Zaccagnini type from its own `X^{θ+δ}`. -/
theorem logFrom_of_theorem2_4 (h : Theorem2_4) {k : ℕ} (hk : 2 ≤ k) :
    ∃ r : ℝ, 7 / 12 * (1 - 1 / (k : ℝ)) < r ∧ r < 1 ∧ LogFrom (EkH k) r := by
  obtain ⟨δ, hδ, hlt, hP⟩ := h k hk
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hθ : 0 ≤ 7 / 12 * (1 - 1 / (k : ℝ)) := by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  refine ⟨7 / 12 * (1 - 1 / (k : ℝ)) + 1 * δ, by linarith, hlt, ?_⟩
  exact logFrom_of_PS (by linarith) (by positivity) hP

/-! ### PROVED: Theorem 1.6 from Perelli 1996, the `7/(36k)` remark at `k = 1` -/

open LeanLab.Perelli1996.EncA in
theorem goldExc_X_eq_EH (N H : ℝ) :
    goldExc (X : ℤ[X]) N H N = EH N H := by
  unfold goldExc EH nRange
  congr 1
  apply Finset.filter_congr
  intro n _
  have hF : Fn (X : ℤ[X]) n = n := by simp [Fn]
  have h2 : (2 : ℤ) ∣ (n : ℤ) ↔ Even n := by rw [even_iff_two_dvd]; norm_cast
  simp only [eval_X, hF, h2]

open LeanLab.Perelli1996.EncA in
theorem admissible_X : Admissible (X : ℤ[X]) := ⟨by simp, by simp⟩

open LeanLab.Perelli1996.EncA in
theorem deg_X : deg (X : ℤ[X]) = 1 := by simp [deg]

open LeanLab.Perelli1996.EncA in
theorem rhoF_X_two : rhoF (X : ℤ[X]) 2 ≠ 0 := by
  rw [rhoF_two]; simp

/-- The remark of Perelli 1996 at `F = x` is Perelli-Pintz's Theorem 1.6, every `ε`. -/
theorem shortLog_of_perelliRemark (h : LeanLab.Perelli1996.EncA.Corollary1bShort (X : ℤ[X])) :
    ShortLog EH (7 / 36) := by
  intro ε hε A hA
  obtain ⟨C, N0, hC⟩ := h admissible_X rhoF_X_two A ε hA hε
  refine ⟨C, N0, fun Y H hY h1 h2 => ?_⟩
  have := hC Y H hY (by rw [deg_X]; norm_num; exact h1) (by rw [deg_X]; norm_num; exact h2)
  rw [deg_X, div_one, Real.rpow_one, goldExc_X_eq_EH] at this
  exact this

theorem theorem1_6_of_perelliRemark (h : LeanLab.Perelli1996.EncA.Corollary1bShort (X : ℤ[X])) :
    Theorem1_6 := fun ε hε _ => shortLog_of_perelliRemark h ε hε

/-- Corollary 1 of Perelli 1996 at `F = x` gives the log saving for `H ≥ X^{1/3+ε}`. -/
theorem shortLog_third_of_perelli (h : LeanLab.Perelli1996.EncA.Corollary1b (X : ℤ[X])) :
    ShortLog EH (1 / 3) := by
  intro ε hε A hA
  obtain ⟨C, N0, hC⟩ := h admissible_X rhoF_X_two A ε hA hε
  refine ⟨C, N0, fun Y H hY h1 h2 => ?_⟩
  have := hC Y H hY (by rw [deg_X]; norm_num; exact h1) (by rw [deg_X]; norm_num; exact h2)
  rw [deg_X, div_one, Real.rpow_one, goldExc_X_eq_EH] at this
  exact this

/-! ### PROVED: the exponent arithmetic of the outlines, p. 226-229 -/

/-- Theorem 1.8 outline: `(7/8)(1/3) = 7/24`, and `Y = X^{7/8+7δ}`, `H = Y^{1/3+6δ}` give
`H = X^{7/24 + 91δ/12 + 42δ²}`. -/
theorem outline1_8 (δ : ℝ) :
    (7 / 8 : ℝ) * (1 / 3) = 7 / 24 ∧
      (7 / 8 + 7 * δ) * (1 / 3 + 6 * δ) = 7 / 24 + 91 / 12 * δ + 42 * δ ^ 2 := by
  constructor <;> ring

/-- QUESTION, PRELIMINARY: that exponent exceeds the stated `7/24 + 7δ` for every `δ > 0`. -/
theorem outline1_8_gap {δ : ℝ} (hδ : 0 < δ) :
    7 / 24 + 7 * δ < (7 / 8 + 7 * δ) * (1 / 3 + 6 * δ) := by nlinarith

/-- With saving `δ/600` fixed, the outline exponent `91/12` would need `m' ≥ 650`:
`(91/12)·600 = 7·650`. -/
theorem outline1_8_reparam : (91 / 12 : ℝ) * 600 = 7 * 650 := by norm_num

/-- Theorem 1.8 outline iv, p. 227: the centre needs `X^{7/12+3δ+ε}`, the periphery reaches
only `X^{7/8+7δ+ε}`. -/
theorem outline1_8_iv (δ ε : ℝ) (hδ : 0 ≤ δ) : 7 / 12 + 3 * δ + ε < 7 / 8 + 7 * δ + ε := by
  linarith

/-- Theorem 2.4 outline, p. 229: `Y = X^{7/12+10δ}`, `H = Y^{1-1/k+δ}` exceed the stated
`X^{7/12(1-1/k)+δ}` by `δ(10(1-1/k) - 5/12) + 10δ²`. -/
theorem outline2_4 (δ k : ℝ) :
    (7 / 12 + 10 * δ) * ((1 - 1 / k) + δ) - (7 / 12 * (1 - 1 / k) + δ) =
      δ * (10 * (1 - 1 / k) - 5 / 12) + 10 * δ ^ 2 := by ring

/-- QUESTION, PRELIMINARY: the gap is positive for `k ≥ 2`, `δ > 0`. -/
theorem outline2_4_gap {δ k : ℝ} (hδ : 0 < δ) (hk : 2 ≤ k) :
    7 / 12 * (1 - 1 / k) + δ < (7 / 12 + 10 * δ) * ((1 - 1 / k) + δ) := by
  have h1 : 1 / k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have := outline2_4 δ k
  nlinarith

/-- Theorem 2.4 outline iv, p. 229: `T ≥ X^{1+7δ} Y^{-1}` and `T ≤ X^{1/2-ε-2δ}` give
`Y ≥ X^{1/2+ε+9δ}`, implied by `Y ≥ X^{7/12+ε+10δ}`. -/
theorem outline2_4_iv (δ ε : ℝ) (hδ : 0 ≤ δ) :
    (1 + 7 * δ) - (1 / 2 - ε - 2 * δ) = 1 / 2 + ε + 9 * δ ∧
      1 / 2 + ε + 9 * δ ≤ 7 / 12 + ε + 10 * δ := by
  constructor <;> [ring; linarith]

/-- The Goldbach exponents in order: `7/108 < 7/36 < 7/24 < 1/3 < 7/12`; Jia's is a third of
Perelli-Pintz's. -/
theorem goldbach_order :
    (7 / 108 : ℝ) < 7 / 36 ∧ (7 / 36 : ℝ) < 7 / 24 ∧ (7 / 24 : ℝ) < 1 / 3 ∧
      (1 / 3 : ℝ) < 7 / 12 ∧ (7 / 108 : ℝ) * 3 = 7 / 36 := by norm_num

/-- Theorem 2.3 at `k = 2` is `7/24`; the base `7/12(1-1/k)` grows with `k` and stays below
`7/12`; the GRH base `(1/2)(1-1/k)` is smaller. -/
theorem hl_exponents {k k' : ℝ} (hk : 2 ≤ k) (hkk : k ≤ k') :
    7 / 12 * (1 - 1 / (2 : ℝ)) = 7 / 24 ∧
      7 / 12 * (1 - 1 / k) ≤ 7 / 12 * (1 - 1 / k') ∧ 7 / 12 * (1 - 1 / k) < 7 / 12 ∧
      1 / 2 * (1 - 1 / k) < 7 / 12 * (1 - 1 / k) := by
  have hk0 : 0 < k := by linarith
  have h1 : 1 / k' ≤ 1 / k := one_div_le_one_div_of_le hk0 hkk
  have h2 : 0 < 1 / k := by positivity
  have h3 : 1 / k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hk0 (by norm_num)]; linarith
  refine ⟨by norm_num, by nlinarith, by nlinarith, by nlinarith⟩

/-- Binary Goldbach makes every `E(X,H)` vanish for `X ≥ 4`. -/
theorem EH_eq_zero_of_binaryGoldbach (h : BinaryGoldbach) {X H : ℝ} (hX : 4 ≤ X) :
    EH X H = 0 := by
  unfold EH
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn ⟨he, hng⟩
  simp only [Finset.mem_Icc] at hn
  have : (4 : ℝ) ≤ n := le_trans hX (Nat.ceil_le.mp hn.1)
  exact hng (h n he (by exact_mod_cast this))

end LeanLab.Languasco2004.EncA

open LeanLab.Languasco2004.EncA in
section
#print axioms theorem1_1
#print axioms EH_mono
#print axioms EkH_mono
#print axioms LogFrom_mono
#print axioms ShortLog_mono
#print axioms shortLog_of_below
#print axioms PS_mono
#print axioms PSdelta_reparam
#print axioms logFrom_of_PS
#print axioms powerSaving_of_PSdelta
#print axioms theorem1_6_of_theorem1_5
#print axioms theorem1_6_all
#print axioms theorem1_1_of_theorem1_8
#print axioms theorem1_1_of_theorem1_7
#print axioms theorem1_1_of_peneva
#print axioms montgomeryVaughan_via_languasco
#print axioms openProblem_reparam
#print axioms li1999_of_li2000
#print axioms zhao_of_pintzAnnounced
#print axioms theorem2_2_of_theorem2_3
#print axioms logFrom_of_theorem2_4
#print axioms goldExc_X_eq_EH
#print axioms admissible_X
#print axioms deg_X
#print axioms rhoF_X_two
#print axioms shortLog_of_perelliRemark
#print axioms theorem1_6_of_perelliRemark
#print axioms shortLog_third_of_perelli
#print axioms outline1_8
#print axioms outline1_8_gap
#print axioms outline1_8_reparam
#print axioms outline1_8_iv
#print axioms outline2_4
#print axioms outline2_4_gap
#print axioms outline2_4_iv
#print axioms goldbach_order
#print axioms hl_exponents
#print axioms EH_eq_zero_of_binaryGoldbach
end
