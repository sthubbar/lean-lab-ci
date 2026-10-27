import LeanLab.GoldbachShort78.LiCounts

/-!
AI wrote the Lean code, Codex task57.
Binary Goldbach is OPEN.
Baker, Harman and Pintz, The difference between consecutive primes, II,
Proc. London Math. Soc. 83, 2001, p. 562, final displayed estimate.
https://doi.org/10.1112/plms/83.3.532
Page image read at https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf
-/

namespace LeanLab.GoldbachShort78

/-- The primes in the real interval `(a, b]`. -/
noncomputable def primeInterval (a b : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌈b⌉₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) ≤ b ∧ p.Prime

/-- Membership in a real prime interval has no rounding condition. -/
theorem mem_primeInterval {a b : ℝ} {p : ℕ} :
    p ∈ primeInterval a b ↔ a < (p : ℝ) ∧ (p : ℝ) ≤ b ∧ p.Prime := by
  classical
  simp only [primeInterval, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨Nat.zero_le _, ?_⟩, h⟩
    exact_mod_cast le_trans h.2.1 (Nat.le_ceil b)

/-- Cited input from BHP 2001 p. 562. The strict count is the printed estimate.
The threshold can be increased to exceed one. -/
def BHPPrintedCount : Prop :=
  ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
    (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t <
      ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ)

/-- Disjoint right tiles contribute their total prime count to the containing window. -/
theorem right_tiles_count {x Y k : ℕ} {B L d : ℝ} (hL : 0 ≤ L)
    (hleft : (x - 2 * Y : ℕ) ≤ B - (k : ℝ) * L) (hright : B ≤ (x - Y : ℕ))
    (hcount : ∀ i ∈ Finset.range k,
      d ≤ ((primeInterval (B - ((i : ℝ) + 1) * L) (B - (i : ℝ) * L)).card : ℝ)) :
    (k : ℝ) * d ≤ ((primeWindow x Y).card : ℝ) := by
  classical
  let tile := fun i : ℕ => primeInterval (B - ((i : ℝ) + 1) * L) (B - (i : ℝ) * L)
  have hdisj : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint tile := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := mem_primeInterval.mp hp
    have hq' := mem_primeInterval.mp hq
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · have hijr : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij'
      nlinarith [mul_nonneg (sub_nonneg.mpr hijr) hL]
    · have hijr : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij'
      nlinarith [mul_nonneg (sub_nonneg.mpr hijr) hL]
  have hsub : (Finset.range k).biUnion tile ⊆ primeWindow x Y := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    have hp' := mem_primeInterval.mp hp
    have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.mp hi
    have hip : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hpl : (x - 2 * Y : ℕ) ≤ p := by
      have : ((x - 2 * Y : ℕ) : ℝ) ≤ p := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hik) hL]
      exact_mod_cast this
    have hpr : p ≤ x - Y := by
      have : (p : ℝ) ≤ (x - Y : ℕ) := by nlinarith [mul_nonneg hip hL]
      exact_mod_cast this
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpl, hpr⟩, hp'.2.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  calc
    (k : ℝ) * d = ∑ i ∈ Finset.range k, d := by simp
    _ ≤ ∑ i ∈ Finset.range k, ((tile i).card : ℝ) := Finset.sum_le_sum hcount
    _ = ((∑ i ∈ Finset.range k, (tile i).card : ℕ) : ℝ) := by simp
    _ ≤ ((primeWindow x Y).card : ℝ) := by exact_mod_cast hcard

/-- Tiles of length L cover at least one quarter of a window of length Y.
The one-tile case preserves the endpoint exponent without an epsilon loss. -/
theorem exists_tile_number {Y L : ℝ} (hL : 0 < L) (hLY : L ≤ Y) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) * L ≤ Y ∧
      (k : ℝ) * L ≤ max (Y / 2) L ∧ Y / 4 ≤ (k : ℝ) * L := by
  by_cases h : 1 ≤ Y / (2 * L)
  · refine ⟨⌊Y / (2 * L)⌋₊, ?_, ?_, ?_, ?_⟩
    · have := (Nat.one_le_floor_iff _).mpr h
      omega
    · have hf := Nat.floor_le (by positivity : 0 ≤ Y / (2 * L))
      have hf' := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hf
      linarith
    · have hf := Nat.floor_le (by positivity : 0 ≤ Y / (2 * L))
      have hf' := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hf
      exact le_trans (by linarith) (le_max_left _ _)
    · have hf := Nat.lt_floor_add_one (Y / (2 * L))
      have hf' := (div_lt_iff₀ (by positivity : 0 < 2 * L)).mp hf
      have hk : (1 : ℝ) ≤ ⌊Y / (2 * L)⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff _).mpr h
      nlinarith [mul_nonneg (sub_nonneg.mpr hk) hL.le]
  · refine ⟨1, by decide, by simpa using hLY, ?_, ?_⟩
    · simpa using le_max_right (Y / 2) L
    · have hy : Y < 2 * L := (div_lt_one (by positivity : 0 < 2 * L)).mp (lt_of_not_ge h)
      simp only [Nat.cast_one, one_mul]
      linarith

/-- A base at least x/4 retains at least one quarter of x^a for 0 ≤ a ≤ 1. -/
theorem quarter_rpow_le {x t a : ℝ} (hx : 0 ≤ x) (ht : x / 4 ≤ t)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : x ^ a / 4 ≤ t ^ a := by
  have ht0 : 0 ≤ t := by linarith
  have h := Real.rpow_le_rpow hx (show x ≤ 4 * t by linarith) ha0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht0] at h
  have h4 : (4 : ℝ) ^ a ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) ha1
    simpa using this
  have htpa : 0 ≤ t ^ a := Real.rpow_nonneg ht0 _
  nlinarith [mul_nonneg (sub_nonneg.mpr h4) htpa]

/-- The printed BHP count at t supplies a full tile of length x^0.525. -/
theorem printed_count_in_tile {x t : ℝ} (ht1 : 1 < t) (hxt : x / 4 ≤ t) (htx : t ≤ x)
    (hcount : (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t <
      ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ)) :
    (9 / 400 : ℝ) * x ^ (0.525 : ℝ) / Real.log x ≤
      ((primeInterval t (t + x ^ (0.525 : ℝ))).card : ℝ) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogs : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) htx
  have hpows := quarter_rpow_le hx0 hxt (by norm_num : (0 : ℝ) ≤ 0.525)
    (by norm_num : (0.525 : ℝ) ≤ 1)
  have hpowup := Real.rpow_le_rpow ht0 htx (by norm_num : (0 : ℝ) ≤ 0.525)
  have hsub : primeInterval t (t + t ^ (0.525 : ℝ)) ⊆
      primeInterval t (t + x ^ (0.525 : ℝ)) := by
    intro p hp
    obtain ⟨hpl, hpr, hpp⟩ := mem_primeInterval.mp hp
    exact mem_primeInterval.mpr ⟨hpl, by linarith, hpp⟩
  calc
    (9 / 400 : ℝ) * x ^ (0.525 : ℝ) / Real.log x ≤
        (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlogx.le
      linarith
    _ ≤ (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t :=
      div_le_div_of_nonneg_left (by positivity) hlogt hlogs
    _ ≤ ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ) := hcount.le
    _ ≤ ((primeInterval t (t + x ^ (0.525 : ℝ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub

/-- CONDITIONAL ON the printed BHP count alone. Tiling supplies the existing window input. -/
theorem bhpWindowCount_of_printed (hin : BHPPrintedCount) :
    ∃ x₀ : ℝ, BHPWindowCount (9 / 1600) x₀ := by
  obtain ⟨T, hT, hC⟩ := hin
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, (4 : ℝ) ≤ x ^ (1 - (0.525 : ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 - 0.525)).eventually_ge_atTop 4
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max (4 * T) (max 1 A), ?_⟩
  intro x hx Y hY hsize
  have hxT : 4 * T ≤ (x : ℝ) := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxA : A ≤ (x : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hxgt : (1 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hxgt
  have hsizeR : 2 * (Y : ℝ) + 3 ≤ x := by exact_mod_cast hsize
  have hYx : Y ≤ x := by omega
  have h2Yx : 2 * Y ≤ x := by omega
  let L : ℝ := (x : ℝ) ^ (0.525 : ℝ)
  have hL : 0 < L := Real.rpow_pos_of_pos hxpos _
  have hsmall : L ≤ (x : ℝ) / 4 := by
    have hprod : L * (x : ℝ) ^ (1 - (0.525 : ℝ)) = x := by
      dsimp [L]
      rw [← Real.rpow_add hxpos]
      norm_num
    have := mul_le_mul_of_nonneg_left (hA x hxA) hL.le
    nlinarith
  obtain ⟨k, hk, hkY, hkmax, hkcover⟩ := exists_tile_number hL hY
  have hkquarter : (k : ℝ) * L ≤ (x : ℝ) / 4 :=
    le_trans hkmax (max_le (by linarith) hsmall)
  have hleft : ((x - 2 * Y : ℕ) : ℝ) ≤ (x : ℝ) - Y - (k : ℝ) * L := by
    rw [Nat.cast_sub h2Yx]
    push_cast
    linarith
  have hright : (x : ℝ) - Y ≤ (x - Y : ℕ) := by
    rw [Nat.cast_sub hYx]
  have htiles := right_tiles_count hL.le hleft hright (d := (9 / 400 : ℝ) * L / Real.log x)
  have hall : ∀ i ∈ Finset.range k,
      (9 / 400 : ℝ) * L / Real.log x ≤
      ((primeInterval ((x : ℝ) - Y - ((i : ℝ) + 1) * L)
        ((x : ℝ) - Y - (i : ℝ) * L)).card : ℝ) := by
    intro i hi
    have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.mp hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    let t := (x : ℝ) - Y - ((i : ℝ) + 1) * L
    have htx4 : (x : ℝ) / 4 ≤ t := by
      dsimp [t]
      nlinarith [mul_nonneg (sub_nonneg.mpr hik) hL.le]
    have htT : T ≤ t := by linarith
    have ht1 : 1 < t := lt_of_lt_of_le hT htT
    have htx : t ≤ x := by
      dsimp [t]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1) hL.le,
        show (0 : ℝ) ≤ Y from Nat.cast_nonneg _]
    have hlocal := printed_count_in_tile ht1 htx4 htx (hC t htT)
    have hend : t + L = (x : ℝ) - Y - (i : ℝ) * L := by dsimp [t]; ring
    change (9 / 400 : ℝ) * L / Real.log x ≤ ((primeInterval t (t + L)).card : ℝ) at hlocal
    rw [hend] at hlocal
    exact hlocal
  have htotal := htiles hall
  calc
    (9 / 1600 : ℝ) * Y / Real.log x ≤ (9 / 400 : ℝ) * ((k : ℝ) * L) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlogx.le
      linarith
    _ = (k : ℝ) * ((9 / 400 : ℝ) * L / Real.log x) := by ring
    _ ≤ ((primeWindow x Y).card : ℝ) := htotal

/-- The interval cardinality is exactly the difference of the usual prime-counting functions. -/
theorem primeInterval_card_eq_primeCounting_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (primeInterval a b).card = Nat.primeCounting ⌊b⌋₊ - Nat.primeCounting ⌊a⌋₊ := by
  classical
  have hb : 0 ≤ b := le_trans ha hab
  have heq : primeInterval a b = Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊ := by
    ext p
    simp only [mem_primeInterval, Finset.mem_sdiff, Nat.mem_primesLE,
      Nat.le_floor_iff hb, Nat.le_floor_iff ha, not_and_or, not_le]
    tauto
  rw [heq, Finset.card_sdiff_of_subset (Nat.primesLE_mono (Nat.floor_mono hab))]
  simp

end LeanLab.GoldbachShort78
