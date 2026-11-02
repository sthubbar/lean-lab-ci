import LeanLab.GoldbachShort78.BHPConsequences

/-!
AI wrote the Lean code, Claude, unit U-1602, run 20261102T0813Z-2382, track T2, NOVELTY triage.
Binary Goldbach is OPEN. Tag: IMPROVEMENT, a sharper constant. Not original.

Source of the claim: research/novelty/P0069-20261101T1637Z.md, section 6 New Result 2, which claims
consecutive Goldbach numbers have gaps at most X^{13/550+ε}. That claim is WRONG as printed: it uses
an almost-all exponent 1/22. R. Li, arXiv 2407.05651 v6, Theorem 1.1 p. 2 prints 1/21.5, and the text
after the end of Section 6 says that 1/22 is far out of reach and gives a lower bound constant below -0.1.
The corrected product is 13/25 times 2/43 = 26/1075, stated below.

Plain math twin of the main theorem `goldbach_short_1075`:
for every ε > 0 and all large x there is an even sum of two primes in [x, x + 3 x^{26/1075 + ε}],
CONDITIONAL ON two cited results:
* `LiRow052`, R. Li, arXiv 2308.04458, Theorem 2 p. 2, the row θ = 0.52: for ε > 0 and large integer n,
  π(n) - π(n - n^{0.52+ε}) ≥ LB n^{0.52+ε} / log n with LB positive. The printed LB differs between
  copies: 0.0300 in the arXiv PDF as fetched 2026-11-02, 0.004 in the author's site PDF, so only some
  positive constant is assumed here.
* `LiPrintedExceptionalCount`, R. Li, arXiv 2407.05651 v6, Theorem 1.1 p. 2, sealed in LiNormalization.

Compare R. Li 2407.05651 Theorem 7.1 p. 27, exponent 21/860 from Baker-Harman-Pintz 0.525.
26/1075 is below 21/860 by 1/4300. The gain is only the swap of 0.525 for Li's own 0.52.

`windowCount_of_backward` is PROVED with no cited input: a backward short interval count at exponent a
gives the window count at the same exponent. The forward BHP route in BHPTiling could not be reused
since the source count here is backward.
-/

namespace LeanLab.GoldbachShort78

open Real

/-- The exponent arithmetic: `13/25 · 2/43 = 26/1075`, below Li's `21/860`, by `1/4300`. -/
theorem exponent_1075 :
    (0.52 : ℝ) * (1 / 21.5) = 26 / 1075 ∧ (26 : ℝ) / 1075 < 21 / 860 ∧
      (21 : ℝ) / 860 - 26 / 1075 = 1 / 4300 := by
  norm_num

/-- The exponent `1/22` of the novelty report is strictly below Li's `1/21.5`, so the report's input
is stronger than the printed theorem; its product `13/550` is below the corrected `26/1075`. -/
theorem report_exponent_stronger :
    (1 : ℝ) / 22 < 1 / 21.5 ∧ (13 : ℝ) / 25 * (1 / 22) = 13 / 550 ∧ (13 : ℝ) / 550 < 26 / 1075 := by
  norm_num

/-- **Cited input**, R. Li, arXiv 2308.04458, Theorem 2 p. 2, row θ = 0.52, with some positive constant
in place of the printed `LB(0.520)`. Integer `n`, backward interval, positive `ε`, as printed. -/
def LiRow052 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 0.005 → ∃ X : ℝ, ∀ n : ℕ, X ≤ n →
    c * (n : ℝ) ^ (0.52 + ε : ℝ) / Real.log n <
      ((primeInterval ((n : ℝ) - (n : ℝ) ^ (0.52 + ε : ℝ)) n).card : ℝ)

/-- PROVED, no cited input: a backward count at exponent `a` gives `WindowCount a (c/32)`.
Tiles have the integer length `⌈x^a⌉`, so that every right endpoint is an integer, as the source needs. -/
theorem windowCount_of_backward {a c X : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hc : 0 < c)
    (hin : ∀ n : ℕ, X ≤ n →
      c * (n : ℝ) ^ a / Real.log n < ((primeInterval ((n : ℝ) - (n : ℝ) ^ a) n).card : ℝ)) :
    ∃ x₀ : ℝ, WindowCount a (c / 32) x₀ := by
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, (8 : ℝ) ≤ x ^ (1 - a) :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - a)).eventually_ge_atTop 8
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max (4 * max X 2) A, ?_⟩
  intro x hx Y hY hsize
  have hxX : 4 * max X 2 ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hxA : A ≤ (x : ℝ) := le_trans (le_max_right _ _) hx
  have hXm : X ≤ max X 2 := le_max_left _ _
  have h2m : (2 : ℝ) ≤ max X 2 := le_max_right _ _
  have hx8 : (8 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsizeR : 2 * (Y : ℝ) + 3 ≤ x := by exact_mod_cast hsize
  have hYx : Y ≤ x := by omega
  have h2Yx : 2 * Y ≤ x := by omega
  set P : ℝ := (x : ℝ) ^ a with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hxpos _
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) ha0
  let Ln : ℕ := ⌈P⌉₊
  let L : ℝ := (Ln : ℝ)
  have hPL : P ≤ L := Nat.le_ceil P
  have hLP : L < P + 1 := Nat.ceil_lt_add_one hP.le
  have hL : 0 < L := by linarith
  have hsmall : L ≤ (x : ℝ) / 4 := by
    have hprod : P * (x : ℝ) ^ (1 - a) = x := by
      rw [hPdef, ← Real.rpow_add hxpos]
      norm_num
    have := mul_le_mul_of_nonneg_left (hA x hxA) hP.le
    nlinarith
  have hLY : L ≤ (Y : ℝ) := by
    have hLnY : Ln ≤ Y := Nat.ceil_le.mpr hY
    change (Ln : ℝ) ≤ (Y : ℝ)
    exact_mod_cast hLnY
  obtain ⟨k, hk, hkY, hkmax, hkcover⟩ := exists_tile_number hL hLY
  have hkquarter : (k : ℝ) * L ≤ (x : ℝ) / 4 :=
    le_trans hkmax (max_le (by linarith) hsmall)
  have hleft : ((x - 2 * Y : ℕ) : ℝ) ≤ (x : ℝ) - Y - (k : ℝ) * L := by
    rw [Nat.cast_sub h2Yx]
    push_cast
    linarith
  have hright : (x : ℝ) - Y ≤ (x - Y : ℕ) := by
    rw [Nat.cast_sub hYx]
  have htiles := right_tiles_count hL.le hleft hright (d := c * (P / 4) / Real.log x)
  have hall : ∀ i ∈ Finset.range k,
      c * (P / 4) / Real.log x ≤
      ((primeInterval ((x : ℝ) - Y - ((i : ℝ) + 1) * L)
        ((x : ℝ) - Y - (i : ℝ) * L)).card : ℝ) := by
    intro i hi
    have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.mp hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hiL : (i : ℝ) * L ≤ (x : ℝ) / 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hik) hL.le]
    have hiLn : i * Ln + Y ≤ x := by
      have : ((i * Ln + Y : ℕ) : ℝ) ≤ x := by
        push_cast
        have : (i : ℝ) * (Ln : ℝ) ≤ (x : ℝ) / 4 := hiL
        linarith
      exact_mod_cast this
    let n : ℕ := x - (i * Ln + Y)
    have hn : (n : ℝ) = (x : ℝ) - Y - (i : ℝ) * L := by
      dsimp [n, L]
      rw [Nat.cast_sub hiLn]
      push_cast
      ring
    have hn4 : (x : ℝ) / 4 ≤ n := by rw [hn]; linarith
    have hnx : (n : ℝ) ≤ x := by
      rw [hn]
      nlinarith [mul_nonneg hi0 hL.le, show (0 : ℝ) ≤ Y from Nat.cast_nonneg _]
    have hnX : X ≤ n := by linarith
    have hn2 : (2 : ℝ) ≤ n := by linarith
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogle : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
    have hcount := hin n hnX
    have hpow4 : P / 4 ≤ (n : ℝ) ^ a := quarter_rpow_le hxpos.le hn4 ha0 ha1.le
    have hpowle : (n : ℝ) ^ a ≤ P := Real.rpow_le_rpow hn0 hnx ha0
    have hsub : primeInterval ((n : ℝ) - (n : ℝ) ^ a) n ⊆
        primeInterval ((x : ℝ) - Y - ((i : ℝ) + 1) * L) ((x : ℝ) - Y - (i : ℝ) * L) := by
      intro p hp
      obtain ⟨hpl, hpr, hpp⟩ := mem_primeInterval.mp hp
      refine mem_primeInterval.mpr ⟨?_, ?_, hpp⟩
      · have : (x : ℝ) - Y - ((i : ℝ) + 1) * L = (n : ℝ) - L := by rw [hn]; ring
        rw [this]
        linarith
      · rw [← hn]
        exact hpr
    calc
      c * (P / 4) / Real.log x ≤ c * (n : ℝ) ^ a / Real.log x := by
        apply div_le_div_of_nonneg_right _ hlogx.le
        exact mul_le_mul_of_nonneg_left hpow4 hc.le
      _ ≤ c * (n : ℝ) ^ a / Real.log n :=
        div_le_div_of_nonneg_left (by positivity) hlogn hlogle
      _ ≤ ((primeInterval ((n : ℝ) - (n : ℝ) ^ a) n).card : ℝ) := hcount.le
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub
  have htotal := htiles hall
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkP : (Y : ℝ) / 8 ≤ (k : ℝ) * P := by
    have hL2 : L ≤ 2 * P := by linarith
    have := mul_le_mul_of_nonneg_left hL2 hk0
    linarith
  calc
    (c / 32) * Y / Real.log x ≤ c * ((k : ℝ) * P / 4) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlogx.le
      nlinarith
    _ = (k : ℝ) * (c * (P / 4) / Real.log x) := by ring
    _ ≤ ((primeWindow x Y).card : ℝ) := htotal

/-- **Goldbach numbers in `[x, x + 3 x^{26/1075+ε}]`**, CONDITIONAL ON `LiRow052` and
`LiPrintedExceptionalCount`. Tag IMPROVEMENT of R. Li, arXiv 2407.05651 v6, Theorem 7.1 p. 27. -/
theorem goldbach_short_1075 (hRow : LiRow052) (hLi : LiPrintedExceptionalCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (26 / 1075 + ε : ℝ) := by
  obtain ⟨c, hc, hrow⟩ := hRow
  let η : ℝ := min (ε / 2) 0.005
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ 0.005 := min_le_right _ _
  obtain ⟨Xr, hXr⟩ := hrow η hη hη2
  have ha0 : (0 : ℝ) < 0.52 + η := by linarith
  have ha1 : (0.52 : ℝ) + η < 1 := by linarith
  obtain ⟨x₀, hW⟩ := windowCount_of_backward ha0.le ha1 hc hXr
  obtain ⟨y₀, hA⟩ := liAlmostAllCountEps_of_printed hLi hη
  have hb0 : (0 : ℝ) ≤ 1 / 21.5 + η := by positivity
  have hb1 : (1 : ℝ) / 21.5 + η ≤ 1 := by
    have : (1 : ℝ) / 21.5 ≤ 1 / 2 := by norm_num
    linarith
  obtain ⟨X, hX⟩ := goldbach_short_b_eventually ha0 ha1 hb0 hb1 (by positivity : 0 < c / 32) hW hA
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hxX : X ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨n, hn, hnx, hupper⟩ := hX x hxX
  have he : (0.52 + η) * (1 / 21.5 + η) ≤ (26 / 1075 + ε : ℝ) := by
    have hexp : (0.52 + η) * (1 / 21.5 + η) = (26 / 1075 : ℝ) + η * (0.52 + 1 / 21.5 + η) := by
      ring_nf
    rw [hexp]
    have hsum : (0.52 : ℝ) + 1 / 21.5 + η ≤ 2 := by
      have : (1 : ℝ) / 21.5 ≤ 1 / 2 := by norm_num
      linarith
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hx1 he
  exact ⟨n, hn, hnx, by linarith⟩

/-- Vacuity for `LiRow052`: its inner count inequality is satisfiable, at `n = 3`, any `a ∈ (0, 1]`,
`c = 1/10`. A local instance only, not a range check. -/
theorem liRow052_local_instance {a : ℝ} (_ha0 : 0 < a) (ha1 : a ≤ 1) :
    (1 / 10 : ℝ) * ((3 : ℕ) : ℝ) ^ a / Real.log (3 : ℕ) <
      ((primeInterval (((3 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) ^ a) (3 : ℕ)).card : ℝ) := by
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hp : (3 : ℝ) ^ a ≤ 3 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ha1
    simpa using this
  have hmem : (3 : ℕ) ∈ primeInterval (((3 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) ^ a) (3 : ℕ) := by
    refine mem_primeInterval.mpr ⟨?_, le_rfl, by norm_num⟩
    have : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
    push_cast
    linarith
  have hcard : (1 : ℝ) ≤ ((primeInterval (((3 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) ^ a) (3 : ℕ)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨3, hmem⟩
  push_cast at hcard ⊢
  have hnum : (1 / 10 : ℝ) * (3 : ℝ) ^ a / Real.log 3 ≤ 3 / 10 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Vacuity for the conclusion of `goldbach_short_1075`: it is met at `x = 8` by `8 = 5 + 3`. -/
theorem goldbach_short_1075_instance (ε : ℝ) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ 8 ≤ n ∧
      (n : ℝ) ≤ ((8 : ℕ) : ℝ) + 3 * ((8 : ℕ) : ℝ) ^ (26 / 1075 + ε : ℝ) := by
  refine ⟨5 + 3, goldbach_add_three (by norm_num) (by norm_num), by norm_num, ?_⟩
  have : (0 : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (26 / 1075 + ε : ℝ) := by positivity
  push_cast
  linarith

end LeanLab.GoldbachShort78

#print axioms LeanLab.GoldbachShort78.exponent_1075
#print axioms LeanLab.GoldbachShort78.report_exponent_stronger
#print axioms LeanLab.GoldbachShort78.windowCount_of_backward
#print axioms LeanLab.GoldbachShort78.goldbach_short_1075
#print axioms LeanLab.GoldbachShort78.liRow052_local_instance
#print axioms LeanLab.GoldbachShort78.goldbach_short_1075_instance
