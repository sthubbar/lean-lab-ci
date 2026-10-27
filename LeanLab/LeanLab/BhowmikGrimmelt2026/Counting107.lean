/-
Counting even multiples in the proof on page 32 of P0029.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

attribute [local instance] Classical.propDecidable

/-- Page 32, even multiples of the conductor in the dyadic interval. -/
noncomputable def evenMultiples107 (r : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun N => Even N ∧ r ∣ N)

/-- LEAF. Page 32, second paragraph. Explicit lower bound from multiples of twice r. -/
theorem even_multiples_lower107 {r : ℕ} (hr : 1 ≤ r) {X : ℝ} (hX : 0 ≤ X) :
    X / (4 * r) - 1 ≤ ((evenMultiples107 r X).card : ℝ) := by
  let a : ℝ := X / (4 * r)
  let b : ℝ := X / (2 * r)
  let K := Finset.Icc ⌈a⌉₊ ⌊b⌋₊
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hinj : Function.Injective (fun k : ℕ => 2 * r * k) := by
    intro k l hkl
    exact mul_left_cancel₀ (by positivity : 2 * r ≠ 0) hkl
  have hsub : K.image (fun k : ℕ => 2 * r * k) ⊆ evenMultiples107 r X := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hkl, hku⟩ := Finset.mem_Icc.mp hk
    have hlo : a ≤ (k : ℝ) := le_trans (Nat.le_ceil a) (by exact_mod_cast hkl)
    have hhi : (k : ℝ) ≤ b := (Nat.le_floor_iff hb).mp hku
    have hl : X / 2 ≤ ((2 * r * k : ℕ) : ℝ) := by
      dsimp [a] at hlo
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * r)] at hlo
      push_cast
      nlinarith
    have hu : ((2 * r * k : ℕ) : ℝ) ≤ X := by
      dsimp [b] at hhi
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)] at hhi
      push_cast
      nlinarith
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hl, Nat.le_floor hu⟩, ?_, ?_⟩
    · exact ⟨r * k, by ring⟩
    · exact ⟨2 * k, by ring⟩
  have hcard : (K.card : ℝ) ≤ ((evenMultiples107 r X).card : ℝ) := by
    exact_mod_cast (show K.card ≤ (evenMultiples107 r X).card from
      (Finset.card_image_of_injective K hinj).symm.trans_le (Finset.card_le_card hsub))
  have hcount : b - a - 1 ≤ (K.card : ℝ) := by
    have hf := Nat.lt_floor_add_one b
    have hc := Nat.ceil_lt_add_one ha
    dsimp [K]
    rw [Nat.card_Icc]
    by_cases hh : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1
    · rw [Nat.cast_sub hh, Nat.cast_add, Nat.cast_one]
      linarith
    · have hh' : (⌊b⌋₊ : ℝ) + 1 < ⌈a⌉₊ := by exact_mod_cast (Nat.lt_of_not_ge hh)
      have hz : (0 : ℝ) ≤ ((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) : ℝ) := by positivity
      linarith
  have hgap : b - a = X / (4 * r) := by
    dsimp [a, b]
    field_simp
    <;> ring
  rw [hgap] at hcount
  exact hcount.trans hcard

/-- LEAF. Page 32, second paragraph. More multiples than the two exceptional sets.
The chosen epsilon is the one printed in the proof. -/
theorem even_multiples_growth107 (A : ℝ) (hA : 5 / 2 < A) (C : ℝ) (hC : 0 ≤ C) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      C * ((r : ℝ) ^ A) ^ (3 / 5 + (1 - 1 / A - 3 / 5) / 2) +
          ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) <
        ((evenMultiples107 r ((r : ℝ) ^ A)).card : ℝ) := by
  let p : ℝ := A * (3 / 5 + (1 - 1 / A - 3 / 5) / 2)
  let q : ℝ := A * (3 / 5)
  let d : ℝ := A - 1
  have hA0 : 0 < A := by linarith
  have hp : p < d := by
    have hp' : p = 4 * A / 5 - 1 / 2 := by dsimp [p]; field_simp; ring
    rw [hp']
    dsimp [d]
    linarith
  have hq : q < d := by dsimp [q, d]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hpt : Filter.Tendsto (fun x : ℝ => x ^ (p - d)) Filter.atTop (nhds 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hp)
  have hqt : Filter.Tendsto (fun x : ℝ => x ^ (q - d)) Filter.atTop (nhds 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hq)
  have hdt := tendsto_rpow_neg_atTop hd
  have ht : Filter.Tendsto (fun x : ℝ => C * x ^ (p - d) + x ^ (q - d) + x ^ (-d))
      Filter.atTop (nhds 0) := by
    simpa using ((hpt.const_mul C).add hqt).add hdt
  have he : ∀ᶠ x : ℝ in Filter.atTop, C * x ^ (p - d) + x ^ (q - d) + x ^ (-d) < 1 / 4 :=
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hn := tendsto_natCast_atTop_atTop.eventually he
  apply Filter.eventually_atTop.mp
  filter_upwards [hn, Filter.eventually_ge_atTop 1] with r he hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrd : 0 < (r : ℝ) ^ d := Real.rpow_pos_of_pos hr0 _
  rw [Real.rpow_sub hr0 p d, Real.rpow_sub hr0 q d, Real.rpow_neg hr0.le d] at he
  have hfrac : (C * (r : ℝ) ^ p + (r : ℝ) ^ q + 1) / (r : ℝ) ^ d < 1 / 4 := by
    convert he using 1 <;> field_simp <;> ring
  have hpoly : C * (r : ℝ) ^ p + (r : ℝ) ^ q + 1 < (r : ℝ) ^ d / 4 := by
    have := (div_lt_iff₀ hrd).mp hfrac
    linarith
  have hl := even_multiples_lower107 hr (Real.rpow_nonneg hr0.le A)
  have hscale : (r : ℝ) ^ A / (4 * r) = (r : ℝ) ^ d / 4 := by
    dsimp [d]
    rw [Real.rpow_sub_one hr0.ne']
    ring
  rw [hscale] at hl
  rw [← Real.rpow_mul hr0.le, ← Real.rpow_mul hr0.le]
  change C * (r : ℝ) ^ p + (r : ℝ) ^ q < _
  exact lt_of_lt_of_le (by linarith only [hpoly]) hl


end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.even_multiples_lower107

#print axioms LeanLab.BhowmikGrimmelt2026.even_multiples_growth107
