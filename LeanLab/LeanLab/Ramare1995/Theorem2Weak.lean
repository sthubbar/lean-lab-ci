import LeanLab.Ramare1995.Statements
import LeanLab.ExceptionalSet.Discharged

/-!
# Ramaré 1995 Theorem 2, weak form, PROVED unconditional

Unit U-1068, PC run 20261019T1403Z-32628. AI wrote this Lean code. KNOWN mathematics.

`theorem2_weak`: there is `c > 0` such that for every `X > exp 67` at least `c X` integers in
`]X, 2X]` are sums of two primes. The constant is INEFFECTIVE: it comes from the density zero
theorem for the Goldbach exceptional set, `LeanLab.ExceptionalSet.vanDerCorput`, which the lab
proves through its Siegel-Walfisz chain, with Siegel's ineffective bound inside. Ramaré's
paper proves the explicit `X/5`; that explicit form stays a cited input of Theorem1.lean.

Proof: for `X` beyond the point where `E(Y) ≤ Y/10`, the evens of `]X, 2X]`, about `X/2` of
them, lose at most `E(2X) ≤ X/5` exceptions, leaving at least `X/8`. For `exp 67 < X` below that
point, Bertrand gives a prime `p` in `]⌊X⌋ - 2, 2⌊X⌋ - 4]` and `p + 2` is a sum of two primes in
`]X, 2X]`, so the count is at least `1`, which is at least `X/X₁`.
-/

open Finset Real Filter

namespace LeanLab.Ramare1995.Theorem2Weak

open LeanLab.Ramare1995

local notation "EE" => LeanLab.ExceptionalSet.E

attribute [local instance] Classical.propDecidable

/-- eventually `E(Y) ≤ Y/10`, from the unconditional density zero theorem -/
theorem E_small : ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 ≤ Y → (EE Y : ℝ) ≤ Y / 10 := by
  have h' : Tendsto (fun X : ℕ => (EE X : ℝ) / X) atTop (nhds 0) :=
    LeanLab.ExceptionalSet.vanDerCorput
  have ev := h'.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1 / 10))
  obtain ⟨Y0, hY0⟩ := eventually_atTop.mp ev
  refine ⟨max Y0 1, fun Y hY => ?_⟩
  have hY1 : (1:ℝ) ≤ Y := by exact_mod_cast le_of_max_le_right hY
  have : (EE Y : ℝ) / Y ≤ 1 / 10 := hY0 Y (le_of_max_le_left hY)
  rw [div_le_iff₀ (by linarith)] at this
  linarith

/-- at least `b/2 - a/2` evens in `]a, b]` -/
theorem card_even_Ioc (a b : ℕ) : b / 2 - a / 2 ≤ ((Ioc a b).filter Even).card := by
  have hsub : (Ioc (a / 2) (b / 2)).image (fun k => 2 * k) ⊆ (Ioc a b).filter Even := by
    intro n hn
    simp only [mem_image, mem_Ioc] at hn
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hn
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, ⟨k, by ring⟩⟩
  calc b / 2 - a / 2 = (Ioc (a / 2) (b / 2)).card := (Nat.card_Ioc _ _).symm
    _ = ((Ioc (a / 2) (b / 2)).image (fun k => 2 * k)).card :=
        (card_image_of_injective _ (fun x y h => by simpa using h)).symm
    _ ≤ _ := card_le_card hsub

/-- evens in `]a, b]`, `a ≥ 3`, are Goldbach sums or exceptions counted by `E b` -/
theorem evens_le (a b : ℕ) (ha : 3 ≤ a) :
    ((Ioc a b).filter Even).card ≤ ((Ioc a b).filter IsGoldbachSum).card + EE b := by
  have hsub : (Ioc a b).filter Even ⊆ (Ioc a b).filter IsGoldbachSum ∪
      (Icc 4 b).filter (fun n => Even n ∧ ¬ IsGoldbachSum n) := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    by_cases hg : IsGoldbachSum n
    · exact mem_union_left _ (by simp [mem_filter, mem_Ioc, hn.1, hg])
    · apply mem_union_right
      simp only [mem_filter, mem_Icc]
      exact ⟨⟨by omega, hn.1.2⟩, hn.2, hg⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  unfold LeanLab.ExceptionalSet.E
  apply le_of_eq
  congr

/-- `goldbachCount X` is the card of the Goldbach filter on `]⌊X⌋, ⌊2X⌋]` -/
theorem goldbachCount_eq (X : ℝ) :
    goldbachCount X = ((Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter IsGoldbachSum).card := by
  unfold goldbachCount
  congr

/-- at least one Goldbach sum in `]X, 2X]` for `X ≥ 4`, from Bertrand -/
theorem one_le_count {X : ℝ} (hX : 6 ≤ X) : 1 ≤ goldbachCount X := by
  rw [goldbachCount_eq]
  set a := ⌊X⌋₊ with ha
  have ha6 : 6 ≤ a := Nat.le_floor (by exact_mod_cast hX)
  have hb : 2 * a ≤ ⌊2 * X⌋₊ := by
    apply Nat.le_floor
    push_cast
    have := Nat.floor_le (show 0 ≤ X by linarith)
    linarith
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (a - 2) (by omega)
  apply card_pos.mpr
  refine ⟨p + 2, ?_⟩
  simp only [mem_filter, mem_Ioc]
  exact ⟨⟨by omega, by omega⟩, ⟨p, 2, hp, Nat.prime_two, rfl⟩⟩

/-- the large range: for `X ≥ max Y0 6`, at least `X/8` Goldbach sums in `]X, 2X]` -/
theorem large_count {Y0 : ℕ} (hY0 : ∀ Y : ℕ, Y0 ≤ Y → (EE Y : ℝ) ≤ Y / 10) {X : ℝ}
    (hX6 : 6 ≤ X) (hXY : (Y0 : ℝ) ≤ X) : X / 8 ≤ goldbachCount X := by
  rw [goldbachCount_eq]
  set a := ⌊X⌋₊ with ha
  set b := ⌊2 * X⌋₊ with hb
  have hX0 : 0 ≤ X := by linarith
  have ha6 : 6 ≤ a := Nat.le_floor (by exact_mod_cast hX6)
  have haX : (a : ℝ) ≤ X := Nat.floor_le hX0
  have hXa : X < a + 1 := Nat.lt_floor_add_one X
  have hbX : (b : ℝ) ≤ 2 * X := Nat.floor_le (by linarith)
  have hab : 2 * a ≤ b := by
    apply Nat.le_floor
    push_cast
    linarith
  have hYb : Y0 ≤ b := by
    have : Y0 ≤ a := Nat.le_floor hXY
    omega
  have hE := hY0 b hYb
  have h1 := card_even_Ioc a b
  have h2 := evens_le a b (by omega)
  -- nat arithmetic: 2 * (b/2 - a/2) ≥ a - 1
  have h3 : a ≤ 2 * (b / 2 - a / 2) + 1 := by omega
  set G := ((Ioc a b).filter IsGoldbachSum).card
  have h4 : (a : ℝ) ≤ 2 * ((G : ℝ) + (EE b : ℝ)) + 1 := by
    have : a ≤ 2 * (G + EE b) + 1 := by omega
    exact_mod_cast this
  linarith

/-- **Ramaré 1995 Theorem 2, weak form, PROVED unconditional** with an ineffective constant -/
theorem theorem2_weak : theorem2_weak_stmt := by
  obtain ⟨Y0, hY0⟩ := E_small
  set X1 : ℝ := max (Y0 : ℝ) 6 with hX1
  have hX1pos : 0 < X1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨min (1 / 8) (1 / X1), lt_min (by norm_num) (by positivity), fun X hX => ?_⟩
  have h67 : (6 : ℝ) ≤ X := by
    have := Real.add_one_le_exp (67 : ℝ)
    linarith
  have hXpos : 0 < X := by linarith
  by_cases hbig : X1 ≤ X
  · have hc := large_count hY0 h67 (le_trans (le_max_left _ _) hbig)
    calc min (1 / 8) (1 / X1) * X ≤ 1 / 8 * X :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hXpos.le
      _ = X / 8 := by ring
      _ ≤ _ := hc
  · push Not at hbig
    have h1 : (1 : ℝ) ≤ goldbachCount X := by exact_mod_cast one_le_count h67
    calc min (1 / 8) (1 / X1) * X ≤ 1 / X1 * X :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hXpos.le
      _ = X / X1 := by ring
      _ ≤ 1 := by rw [div_le_one hX1pos]; exact hbig.le
      _ ≤ _ := h1

/-- vacuity: the hypothesis range is nonempty and the count is positive there, e.g. at `X = 6`
the integers `7 .. 12` include `8 = 3 + 5`. -/
theorem vacuity : 1 ≤ goldbachCount 6 := one_le_count le_rfl

end LeanLab.Ramare1995.Theorem2Weak
