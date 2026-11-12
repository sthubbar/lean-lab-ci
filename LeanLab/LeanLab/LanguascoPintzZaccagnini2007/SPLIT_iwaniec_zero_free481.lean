import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
A cut of the nonreal primitive character zero free region of the second proof
paragraph after display 10 into three steps: the arithmetic edge of the region
denominator, the classically known half plane at real part one and above, and the
open strip below one where the analytic content of the region sits. The region
edge is placed on the nonnegative axis in the assembly, which is where the
denominator bound is used.

Source check. The constant and the region in `iwaniecDenom481`, namely
`B = 4 * 10 ^ 4 * (log (2 r') + (l log (2 l)) ^ (3 / 4))` with `l = log (r (|t| + 2))` and
zero free part `re s > 1 - 1 / B`, were verified only against the page image of P0045 page 6.
The text extraction papers/P0045.txt drops the bracket after `4 * 10 ^ 4`, so it reads as if the
factor multiplied the first summand only; do not audit this constant from the txt. Iwaniec 1974
itself is not in papers, so the constant is checked against P0045 only, not against the cited
theorem. The half plane leaf does not use primitivity, a harmless strengthening. Note added by
architect U-1649.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF. Step one, the arithmetic edge of the region: for a positive modulus the
denominator of the region is at least one, so the edge one minus its reciprocal is
nonnegative and strictly below one. -/
theorem iwaniec_denom_ge_one481 (r : ℕ) (hr : 1 ≤ r) (t : ℝ) :
    (1 : ℝ) ≤ iwaniecDenom481 r t := by
  dsimp [iwaniecDenom481]
  have h1 : 1 ≤ (oddRad131 r : ℝ) := by
    have h_pos : 1 ≤ oddRad131 r := by
      dsimp [oddRad131]
      apply Nat.one_le_of_lt
      apply Finset.prod_pos
      intro p hp
      rw [Finset.mem_filter] at hp
      omega
    exact_mod_cast h_pos

  have h2 : 2 ≤ 2 * (oddRad131 r : ℝ) := by linarith
  have h3 : Real.log 2 ≤ Real.log (2 * (oddRad131 r : ℝ)) := by
    apply Real.log_le_log (by norm_num) h2

  have hl_base : 2 ≤ (r : ℝ) * (|t| + 2) := by
    have hr_re : 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have ht : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hlog2 : Real.log 2 ≤ Real.log ((r : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by norm_num) hl_base

  have h_log2_pos : 0 < Real.log 2 := by
    apply Real.log_pos (by norm_num)

  have hl2_pos : 0 ≤ Real.log ((r : ℝ) * (|t| + 2)) * Real.log (2 * Real.log ((r : ℝ) * (|t| + 2))) := by
    have hl_pos : 0 ≤ Real.log ((r : ℝ) * (|t| + 2)) := le_of_lt (lt_of_lt_of_le h_log2_pos hlog2)
    have hl2_inner_pos : 0 ≤ Real.log (2 * Real.log ((r : ℝ) * (|t| + 2))) := by
      apply Real.log_nonneg
      have hl_inner_2 : 2 * Real.log 2 ≤ 2 * Real.log ((r : ℝ) * (|t| + 2)) := by nlinarith
      have he : Real.exp 1 < 4 := by
        calc
          Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          _ ≤ 4 := by norm_num
      have log2_ge : (1/2 : ℝ) ≤ Real.log 2 := by
        have he2 : Real.exp (1/2 : ℝ) * Real.exp (1/2 : ℝ) ≤ 2 * 2 := by
          rw [← Real.exp_add]
          norm_num
          exact le_of_lt he
        have he3 : Real.exp (1/2 : ℝ) ≤ 2 := by
          nlinarith [Real.exp_pos (1/2 : ℝ)]
        have he4 := Real.log_le_log (Real.exp_pos _) he3
        rw [Real.log_exp] at he4
        exact he4
      have : (1 : ℝ) ≤ 2 * Real.log 2 := by nlinarith [log2_ge]
      linarith
    positivity
  have hpow_pos : 0 ≤ (Real.log ((r : ℝ) * (|t| + 2)) * Real.log (2 * Real.log ((r : ℝ) * (|t| + 2)))) ^ (3/4 : ℝ) := by
    apply Real.rpow_nonneg
    exact hl2_pos

  have hl_final : (1 : ℝ) ≤ 4 * 10^4 * Real.log 2 := by
    have he : Real.exp 1 < 4 := by
      calc
        Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        _ ≤ 4 := by norm_num
    have log2_ge : (1/2 : ℝ) ≤ Real.log 2 := by
      have he2 : Real.exp (1/2 : ℝ) * Real.exp (1/2 : ℝ) ≤ 2 * 2 := by
        rw [← Real.exp_add]
        norm_num
        exact le_of_lt he
      have he3 : Real.exp (1/2 : ℝ) ≤ 2 := by
        nlinarith [Real.exp_pos (1/2 : ℝ)]
      have he4 := Real.log_le_log (Real.exp_pos _) he3
      rw [Real.log_exp] at he4
      exact he4
    nlinarith [log2_ge]

  linarith

/-- LEAF. Step two, the half plane at real part one and above: a nonreal primitive
character does not vanish there, independently of the region denominator. -/
theorem iwaniec_no_zero_half_plane481 (r : ℕ) (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hs : 1 ≤ s.re) : Lfun481 χ s ≠ 0 := by
  have hr0 : r ≠ 0 := by omega
  haveI : NeZero r := ⟨hr0⟩
  have hne : χ ≠ 1 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hnonreal
    have h1 : ((1 : DirichletCharacter ℂ r) a).im = 0 := by
      by_cases hu : IsUnit a
      · simp [MulChar.one_apply hu]
      · simp [MulChar.map_nonunit _ hu]
    exact ha h1
  have hL : Lfun481 χ s = DirichletCharacter.LFunction χ s := by
    simp only [Lfun481, dif_neg hr0]
  rw [hL]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hs

/-- LEAF. Step three, the open strip below one: a nonreal primitive character does
not vanish strictly between real part zero and one once it lies to the right of the
region edge. This is the analytic content of the region, cut out of the half plane
at one which step two covers. -/
theorem iwaniec_no_zero_open_strip481 (r : ℕ) (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re) : Lfun481 χ s ≠ 0 := by
  sorry

/-- The region edge sits at nonnegative real part, which is the only place the
denominator bound of step one is needed. -/
private theorem iwaniec_region_pos481 (r : ℕ) (hr : 1 ≤ r) (t : ℝ) {x : ℝ}
    (hx : 1 - 1 / iwaniecDenom481 r t < x) : 0 < x := by
  have h1 : (1 : ℝ) ≤ iwaniecDenom481 r t := iwaniec_denom_ge_one481 r hr t
  have hD : (0 : ℝ) < iwaniecDenom481 r t := lt_of_lt_of_le zero_lt_one h1
  have hq : 1 / iwaniecDenom481 r t ≤ 1 := by
    rw [div_le_iff₀ hD]
    simpa using h1
  linarith

/-- The nonreal primitive character zero free region, from its three steps: the
half plane at one and above, and the strip below one split by the region edge, which
step one keeps on the nonnegative axis. -/
theorem iwaniec_zero_free481_split : IwaniecStatement481 := by
  intro r hr χ hprim hnonreal s hs
  rcases lt_or_ge s.re (1 : ℝ) with hlt | hge
  · exact iwaniec_no_zero_open_strip481 r hr χ hprim hnonreal hlt
      (iwaniec_region_pos481 r hr s.im hs) hs
  · exact iwaniec_no_zero_half_plane481 r hr χ hprim hnonreal hge

end

end LeanLab.LPZ2007
