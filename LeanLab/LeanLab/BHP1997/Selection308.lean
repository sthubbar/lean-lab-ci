/-
BHP1997, page 46, Lemma 31. Full scalar parameter selection.
The epsilon cutoff depends on the fixed phi and j.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Lemma31

namespace LeanLab.BHP1997.Task308

/-- Page 46, Lemma 31, displays 5.8 and 5.9. For fixed phi in the printed interval,
a sufficiently small positive epsilon permits the integer h and alpha selection.
The implied bound on h is made explicit as h at most two divided by lambda. -/
theorem lemma31_selection (j : ℕ) (hj : 4 ≤ j) (φ : ℝ)
    (hφl : 1 / (2 * (j : ℝ) + 2) < φ) (hφu : φ ≤ 1 / (2 * (j : ℝ))) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η → ∀ lam : ℝ,
      0 < lam → lam ≤ φ / (1 - φ) + 1 / (2 * (j : ℝ) - 1 + 2 * ε) →
      ∃ (α : ℝ) (h : ℕ), ε ≤ α ∧ α ≤ 1 ∧ j ≤ h ∧ (h : ℝ) ≤ 2 / lam ∧
        2 / (2 * (h : ℝ) + α) ≤ lam ∧
        lam ≤ φ / (1 - φ) + 1 / (2 * (h : ℝ) - 1 + 2 * α) := by
  have hjR : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hp := Lemma31.phi_ratio (by linarith : (1 : ℝ) ≤ j) hφl hφu
  let δ := φ / (1 - φ) - 1 / (2 * (j : ℝ) + 1)
  have hδ : 0 < δ := sub_pos.mpr hp.1
  refine ⟨min 1 (δ / 4), lt_min (by norm_num) (by positivity), ?_⟩
  intro ε hε hεη lam hl hlup
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hεη (min_le_left _ _)).le
  have hεsmall : ε < δ / 4 := lt_of_lt_of_le hεη (min_le_right _ _)
  have hεmargin : 2 * ε < φ / (1 - φ) - 1 / (2 * (j : ℝ) + 1) := by
    dsimp [δ] at hδ hεsmall
    linarith
  have hdj : 0 < 2 * (j : ℝ) - 1 := by linarith
  have hlstrict : lam < 2 / (2 * (j : ℝ) - 1) := by
    have hh := one_div_lt_one_div_of_lt hdj
      (show 2 * (j : ℝ) - 1 < 2 * (j : ℝ) - 1 + 2 * ε by linarith)
    calc
      lam ≤ φ / (1 - φ) + 1 / (2 * (j : ℝ) - 1 + 2 * ε) := hlup
      _ < 1 / (2 * (j : ℝ) - 1) + 1 / (2 * (j : ℝ) - 1) :=
        add_lt_add_of_le_of_lt hp.2 hh
      _ = _ := by ring
  have hl1 : lam ≤ 1 := by
    have hh : 2 / (2 * (j : ℝ) - 1) ≤ 1 := by
      rw [div_le_iff₀ hdj]
      linarith
    exact hlstrict.le.trans hh
  have hcancel : lam * (1 / lam) = 1 := by field_simp
  have hcancel2 : lam * (2 / lam) = 2 := by field_simp
  have htwo : 2 / lam = 2 * (1 / lam) := by ring
  let h : ℕ := ⌊1 / lam + 1/2⌋₊
  have hfloor : (h : ℝ) ≤ 1 / lam + 1/2 := Nat.floor_le (by positivity)
  have hfloorlt : 1 / lam + 1/2 < (h : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjh : j ≤ h := by
    change j ≤ ⌊1 / lam + 1/2⌋₊
    rw [Nat.le_floor_iff (by positivity)]
    have hh : (j : ℝ) - 1/2 ≤ 1 / lam := by
      rw [le_div_iff₀ hl]
      have ht := (lt_div_iff₀ hdj).mp hlstrict
      nlinarith only [ht]
    linarith
  have hhR : (1 : ℝ) ≤ h := by
    have hh : 4 ≤ h := hj.trans hjh
    exact_mod_cast (show 1 ≤ h by omega)
  have hhsize : (h : ℝ) ≤ 2 / lam := by
    have hhalf : (1/2 : ℝ) ≤ 1 / lam := by
      rw [le_div_iff₀ hl]
      linarith
    calc
      (h : ℝ) ≤ 1 / lam + 1/2 := hfloor
      _ ≤ 1 / lam + 1 / lam := by linarith
      _ = _ := by ring
  have hinterval : lam ≤ 2 / (2 * (h : ℝ) - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 * (h : ℝ) - 1)).2
    nlinarith only [mul_le_mul_of_nonneg_left hfloor hl.le, hcancel]
  by_cases hcase : ε ≤ 2 / lam - 2 * (h : ℝ)
  · let α := 2 / lam - 2 * (h : ℝ)
    have hα0 : 0 ≤ α := hε.le.trans hcase
    have hα1 : α ≤ 1 := by
      dsimp [α]
      rw [htwo]
      linarith only [hfloorlt]
    have heq : 2 / (2 * (h : ℝ) + α) = lam := by
      have he : 2 * (h : ℝ) + α = 2 / lam := by dsimp [α]; ring
      rw [he]
      field_simp
    have hhj : (j : ℝ) ≤ h := by exact_mod_cast hjh
    have hratio : 1 / (2 * (h : ℝ) + 1) ≤ φ / (1 - φ) := by
      exact (div_le_div_of_nonneg_left (by norm_num)
        (by linarith : 0 < 2 * (j : ℝ) + 1) (by linarith)).trans hp.1.le
    have hcalc := Lemma31.case2 hhR hα0 hα1
    refine ⟨α, h, hcase, hα1, hjh, hhsize, heq.le, ?_⟩
    rw [heq] at hcalc
    linarith
  · have hlower : 2 / (2 * (h : ℝ) + ε) ≤ lam := by
      apply (div_le_iff₀ (by linarith : 0 < 2 * (h : ℝ) + ε)).2
      have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hcase) hl
      nlinarith only [hh, hcancel2]
    refine ⟨ε, h, le_rfl, hε1, hjh, hhsize, hlower, ?_⟩
    by_cases heq : h = j
    · simpa only [heq] using hlup
    · have hjh' : j + 1 ≤ h := by omega
      have hjhR : (j : ℝ) + 1 ≤ h := by exact_mod_cast hjh'
      let d : ℝ := 2 * (h : ℝ) - 1
      have hd1 : 1 ≤ d := by dsimp [d]; linarith
      have hd : 0 < d := by linarith
      have hdε : 0 < d + 2 * ε := by linarith
      have hprod : 1 ≤ d * (d + 2 * ε) := by
        have hsecond : 1 ≤ d + 2 * ε := by linarith
        nlinarith only [mul_le_mul_of_nonneg_left hsecond hd.le, hd1]
      have hinv : 1 / d ≤ 1 / (2 * (j : ℝ) + 1) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
        dsimp [d]
        linarith
      have hquot : (2 * ε) / (d * (d + 2 * ε)) ≤ 2 * ε := by
        rw [div_le_iff₀ (mul_pos hd hdε)]
        nlinarith only [mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ 2 * ε)]
      have he : 2 / d - 1 / (d + 2 * ε) = 1 / d +
          (2 * ε) / (d * (d + 2 * ε)) := by
        field_simp
        <;> ring
      have hdiff : 2 / d - 1 / (d + 2 * ε) ≤ 1 / d + 2 * ε := by
        rw [he]
        linarith
      change lam ≤ φ / (1 - φ) + 1 / (d + 2 * ε)
      change lam ≤ 2 / d at hinterval
      linarith


/-- Page 46. A nonvacuous rational instance for both displayed inequalities.
Take j and h equal to four, phi one eighth, lambda one quarter
and alpha and epsilon one thousandth. -/
theorem lemma31_selection_instance :
    let j : ℕ := 4
    let φ : ℝ := 1/8
    let ε : ℝ := 1/1000
    let lam : ℝ := 1/4
    let α : ℝ := ε
    let h : ℕ := 4
    1 / (2 * (j : ℝ) + 2) < φ ∧ φ ≤ 1 / (2 * (j : ℝ)) ∧
      0 < ε ∧ ε < min 1 ((φ / (1-φ) - 1/(2*(j:ℝ)+1))/4) ∧
      0 < lam ∧ lam ≤ φ / (1-φ) + 1/(2*(j:ℝ)-1+2*ε) ∧
      ε ≤ α ∧ α ≤ 1 ∧ j ≤ h ∧ (h:ℝ) ≤ 2/lam ∧
      2/(2*(h:ℝ)+α) ≤ lam ∧ lam ≤ φ/(1-φ)+1/(2*(h:ℝ)-1+2*α) := by
  norm_num

end LeanLab.BHP1997.Task308
