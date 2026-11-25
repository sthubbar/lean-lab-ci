/-
Split of `zero_reciprocal_multiplicity508` of `SPLIT_oscillatory_zero_modes508` into two
cited leaves and a proved assembly.

Source: P0029 pages 11 and 12, display 3.7, the zero sum over the zeros up to height `T`
weighted by multiplicity and the reciprocal of the norm. The lab statement drops the zero
bound hypothesis `Re ρ ≤ Θ` that the paper carries, so a zero close to the origin is not
excluded by the hypothesis; by the functional equation it is the reflection of a zero close
to `1`. RouteCount508 proves the statement with the hypothesis kept. Without it the only
extra input is a lower bound for `1 - Re ρ` at low height, which is the classical zero free
region together with Siegel's theorem for the one possible exceptional real zero:

* LEAF A, Davenport chapter 14: a primitive character has no zero with `|Im ρ| ≤ 1` and
  `1 - Re ρ` below a constant over `log (3 q)`, except possibly one real zero of a real
  character.
* LEAF B, Davenport chapter 21, Siegel's theorem: a real zero `β` of a primitive real
  character satisfies `1 - β ≥ c(ε) q^(-ε)`.

The assembly reflects every strip zero through the functional equation, uses the two
leaves to keep it at distance `c q^(-ε)` from the origin, and sums the reciprocal weights
over unit windows with the proved window count `zero_window_count_full508`. The loss
against RouteCount508 is the factor `X^(ε/2)` from the low window, absorbed in `X^ε`.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp508a
import LeanLab.BhowmikGrimmelt2026.Decomp541a
import LeanLab.BhowmikGrimmelt2026.RouteWindow508
import LeanLab.PNTPort.DirichletZF.ZeroFreeSiegel
import LeanLab.BhowmikGrimmelt2026.LEAF_feed1122_zero_reciprocal508_p2_box

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 page 11 display 3.7 without the hypothesis `Re ρ ≤ Θ` needs the zeros of
the Riemann zeta function, the L function of the one primitive character modulo one, kept
away from the origin; by the functional equation that is a zero free box at `1`. The
classical fact used: zeta has no zero in the open critical strip with `|Im ρ| ≤ 1`, its
first zero having ordinate about `14.13`, see Titchmarsh, The Theory of the Riemann Zeta
Function, chapter 15, or Davenport chapter 15. Class HARD, a numerical analytic step:
the zero free region already in PNTPort, `ZeroInequalitySpec` of StrongPNT, starts at
height `2`. -/
theorem leaf_zeta_no_low_zero508 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 < |ρ.im| :=
  zeta_no_low_zero_from_box508

/-- At height at most one, every strip zero of a primitive character modulo `q` has
`1 - Re ρ ≥ c q^(-ε)`, with `0 < c ≤ 1`. For a non principal character this is the
proved zero free region with Siegel's theorem, `zero_free_siegel` of PNTPort, Davenport
chapters 14 and 21, since at height at most one `c / log (Bt q t)` beats a multiple of
`q^(-ε)`. The principal primitive character lives modulo one and is zeta, handled by
`leaf_zeta_no_low_zero508`. CONDITIONAL ON `leaf_zeta_no_low_zero508` only. -/
theorem low_zero_gap_from_leaves508 (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re →
        ρ.re < 1 → |ρ.im| ≤ 1 → c * (q : ℝ) ^ (-ε) ≤ 1 - ρ.re := by
  obtain ⟨c, hc, hzf⟩ := LeanLab.PNTPort.DirichletZF.zero_free_siegel ε hε
  have hZ : 0 ≤ LeanLab.PNTPort.DirichletZF.Z := tsum_nonneg (fun _ => norm_nonneg _)
  set W : ℝ := 8 * LeanLab.PNTPort.DirichletZF.Z + 1 with hW
  have hW1 : 1 ≤ W := by rw [hW]; linarith
  have hWε : (0 : ℝ) < W ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  refine ⟨min 1 (min c (c * ε / W ^ ε)), ?_, min_le_left _ _, ?_⟩
  · exact lt_min one_pos (lt_min hc (by positivity))
  intro q _ χ hχ ρ hρ h0 h1 him
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hqe : (0 : ℝ) < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hq0 _
  by_cases hχ1 : χ = 1
  · exfalso
    have hcond : χ.conductor = q := hχ
    rw [hχ1, DirichletCharacter.conductor_one] at hcond
    subst hcond
    rw [DirichletCharacter.LFunction_modOne_eq] at hρ
    have := leaf_zeta_no_low_zero508 ρ hρ h0 h1
    linarith
  have hz := hzf q χ hχ1 ρ hρ
  have hBt1 : 1 < LeanLab.PNTPort.DirichletZF.Bt q ρ.im :=
    LeanLab.PNTPort.DirichletZF.one_lt_Bt (N := q) ρ.im
  have hlogpos : 0 < Real.log (LeanLab.PNTPort.DirichletZF.Bt q ρ.im) := Real.log_pos hBt1
  have hBtle : LeanLab.PNTPort.DirichletZF.Bt q ρ.im ≤ W * (q : ℝ) := by
    show 2 * (q : ℝ) * (|ρ.im| + 3) * LeanLab.PNTPort.DirichletZF.Z ≤ W * (q : ℝ)
    rw [hW]
    have h4 : |ρ.im| + 3 ≤ 4 := by linarith
    have : 2 * (q : ℝ) * (|ρ.im| + 3) * LeanLab.PNTPort.DirichletZF.Z ≤
        2 * (q : ℝ) * 4 * LeanLab.PNTPort.DirichletZF.Z := by
      apply mul_le_mul_of_nonneg_right _ hZ
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  have hlog : Real.log (LeanLab.PNTPort.DirichletZF.Bt q ρ.im) ≤ (W * (q : ℝ)) ^ ε / ε :=
    (Real.log_le_log (by linarith) hBtle).trans
      (Real.log_le_rpow_div (by positivity) hε)
  have hsplit : (W * (q : ℝ)) ^ ε = W ^ ε * (q : ℝ) ^ ε :=
    Real.mul_rpow (by linarith) hq0.le
  have hqinv : (q : ℝ) ^ (-ε) * (q : ℝ) ^ ε = 1 := by
    rw [← Real.rpow_add hq0]; simp
  have hkey : c * ε / W ^ ε * (q : ℝ) ^ (-ε) ≤
      c / Real.log (LeanLab.PNTPort.DirichletZF.Bt q ρ.im) := by
    rw [le_div_iff₀ hlogpos]
    calc c * ε / W ^ ε * (q : ℝ) ^ (-ε) * Real.log (LeanLab.PNTPort.DirichletZF.Bt q ρ.im)
        ≤ c * ε / W ^ ε * (q : ℝ) ^ (-ε) * ((W * (q : ℝ)) ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = c * ((q : ℝ) ^ (-ε) * (q : ℝ) ^ ε) := by
          rw [hsplit]; field_simp
      _ = c := by rw [hqinv, mul_one]
  have hmin : min 1 (min c (c * ε / W ^ ε)) * (q : ℝ) ^ (-ε) ≤
      min (c / Real.log (LeanLab.PNTPort.DirichletZF.Bt q ρ.im)) (c * (q : ℝ) ^ (-ε)) := by
    apply le_min
    · calc min 1 (min c (c * ε / W ^ ε)) * (q : ℝ) ^ (-ε)
          ≤ c * ε / W ^ ε * (q : ℝ) ^ (-ε) :=
            mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hqe.le
        _ ≤ _ := hkey
    · exact mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hqe.le
  linarith

/-- Every strip zero of any character modulo `q`, primitive or not, has norm at least
`c q^(-ε)`. The zero is a zero of the primitive character inducing `χ`, by
`character_zero_changeLevel508`; its reflection `1 - ρ` is a zero of the inverse
primitive character by `primitive_zero_reflection541`; at height at most one the gap of
`low_zero_gap_from_leaves508` gives `Re ρ ≥ c r^(-ε) ≥ c q^(-ε)`, and above height one the
norm exceeds one. -/
theorem zero_norm_lower_from_leaves508 (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        c * (q : ℝ) ^ (-ε) ≤ ‖ρ‖ := by
  obtain ⟨c, hc0, hc1, hgap⟩ := low_zero_gap_from_leaves508 ε hε
  refine ⟨c, hc0, hc1, ?_⟩
  intro q _ χ ρ hρ h0 h1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqe1 : (q : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  rcases le_or_gt |ρ.im| 1 with hlow | hhigh
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hd := χ.conductor_dvd_level
    have hz : DirichletCharacter.LFunction χ ρ = 0 ↔
        DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
      simpa only [χ.changeLevel_primitiveCharacter] using
        character_zero_changeLevel508 hd χ.primitiveCharacter h0 h1
    have hprim := χ.primitiveCharacter_isPrimitive
    have hr := primitive_zero_reflection541 χ.primitiveCharacter hprim (hz.mp hρ) h0 h1
    have hinv : (χ.primitiveCharacter)⁻¹.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hprim
    have hg := hgap χ.conductor (χ.primitiveCharacter)⁻¹ hinv (1 - ρ) hr
      (by simp; linarith) (by simp; linarith) (by simpa using hlow)
    simp only [Complex.sub_re, Complex.one_re, sub_sub_cancel] at hg
    have hr1 : (1 : ℝ) ≤ χ.conductor := by
      exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hrq : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hd
    have hmono : (q : ℝ) ^ (-ε) ≤ (χ.conductor : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hrq (by linarith)
    have hn : ρ.re ≤ ‖ρ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    calc c * (q : ℝ) ^ (-ε) ≤ c * (χ.conductor : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_left hmono hc0.le
      _ ≤ ρ.re := hg
      _ ≤ ‖ρ‖ := hn
  · have him : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have : c * (q : ℝ) ^ (-ε) ≤ 1 := by
      calc c * (q : ℝ) ^ (-ε) ≤ 1 * 1 :=
            mul_le_mul hc1 hqe1 (Real.rpow_nonneg (by linarith) _) zero_le_one
        _ = 1 := by ring
    linarith

/-- The reciprocal weights of the integer windows sum to at most twice a harmonic sum.
The same estimate as `int_abs_harmonic508` of RouteCount508, which this file cannot import
since RouteCount508 imports `SPLIT_oscillatory_zero_modes508`. -/
theorem int_abs_harmonic_feed508 (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N, 1 / (|(k : ℝ)| + 1) ≤
      2 * (1 + Real.log ((N : ℝ) + 1)) := by
  have hsub : Finset.Icc (-(N : ℤ)) N ⊆
      (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)) ∪
        (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases le_total 0 k with h | h
    · left; exact ⟨k.toNat, by rw [Finset.mem_range]; omega, by omega⟩
    · right; exact ⟨(-k).toNat, by rw [Finset.mem_range]; omega, by omega⟩
  have hh : ∑ j ∈ Finset.range (N + 1), 1 / ((j : ℝ) + 1) ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have h := harmonic_le_one_add_log (N + 1)
    rw [harmonic] at h
    push_cast at h
    simpa [one_div] using h
  have h1 : ∑ k ∈ (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)), 1 / (|(k : ℝ)| + 1) =
      ∑ j ∈ Finset.range (N + 1), 1 / ((j : ℝ) + 1) := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have h2 : ∑ k ∈ (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)), 1 / (|(k : ℝ)| + 1) =
      ∑ j ∈ Finset.range (N + 1), 1 / ((j : ℝ) + 1) := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hun := Finset.sum_union_inter
    (s₁ := (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)))
    (s₂ := (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)))
    (f := fun k : ℤ => 1 / (|(k : ℝ)| + 1))
  have hint : (0 : ℝ) ≤ ∑ k ∈ (Finset.range (N + 1)).image (fun j : ℕ => (j : ℤ)) ∩
      (Finset.range (N + 1)).image (fun j : ℕ => -(j : ℤ)), 1 / (|(k : ℝ)| + 1) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℤ => 1 / (|(k : ℝ)| + 1))
    hsub (fun _ _ _ => by positivity)
  rw [h1, h2] at hun
  linarith

/-- `zero_reciprocal_multiplicity508`, the statement of `SPLIT_oscillatory_zero_modes508`
unchanged, assembled from the two leaves of this file and the proved window count. The
zeros are sorted by the integer part of the ordinate as in RouteCount508; a zero in the
window `k` has `|k| + 1 ≤ ‖ρ‖ + 2 ≤ 3 ‖ρ‖ / m` with `m = c X^(-ε/2)` its norm lower bound,
so the window weight is `(3 / m) / (|k| + 1)` and the harmonic sum gives
`log² X · X^(ε/2) ≪ X^ε`. CONDITIONAL on `leaf_zeta_no_low_zero508`
only. -/
theorem zero_reciprocal_multiplicity508_from_leaves (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X →
      ∀ χ : DirichletCharacter ℂ q, ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ ≤ K * (X : ℝ) ^ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨A, hA0, hA⟩ := zero_window_count_full508
  obtain ⟨c, hc0, hc1, hnorm⟩ := zero_norm_lower_from_leaves508 (ε / 2) hε2
  refine ⟨120 * A / c * (2 / (ε / 2)) ^ 2, by positivity, ?_⟩
  intro X hX2 q _ hqQ χ T hT Z hZset
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXp : (0 : ℝ) < X := by linarith
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hXr
  have hL0 : 0 ≤ Real.log X := by have := Real.log_two_gt_d9; linarith
  have h3 : 2 * (X : ℝ) + 4 ≤ (X : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hXr) (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ 2 + 2 * X + 2)]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqX : (q : ℝ) ≤ X := by exact_mod_cast hqQ.trans (Nat.sqrt_le_self X)
  -- the norm lower bound `m = c X^(-ε/2)`
  set m : ℝ := c * (X : ℝ) ^ (-(ε / 2)) with hm
  have hXe : (0 : ℝ) < (X : ℝ) ^ (-(ε / 2)) := Real.rpow_pos_of_pos hXp _
  have hXe1 : (X : ℝ) ^ (-(ε / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
  have hm0 : 0 < m := mul_pos hc0 hXe
  have hm1 : m ≤ 1 := by
    calc m ≤ 1 * 1 := mul_le_mul hc1 hXe1 hXe.le zero_le_one
      _ = 1 := by ring
  have hmX : ∀ ρ ∈ Z, m ≤ ‖ρ‖ := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, -⟩ := (hZset ρ).mp hρ
    have hb := hnorm q χ ρ hz h0 h1
    have hmono : (X : ℝ) ^ (-(ε / 2)) ≤ (q : ℝ) ^ (-(ε / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hqX (by linarith)
    calc m ≤ c * (q : ℝ) ^ (-(ε / 2)) := mul_le_mul_of_nonneg_left hmono hc0.le
      _ ≤ ‖ρ‖ := hb
  have hmaps : ∀ ρ ∈ Z, ⌊ρ.im⌋ ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ) := by
    intro ρ hρ
    obtain ⟨-, -, -, him⟩ := (hZset ρ).mp hρ
    have h2 : |ρ.im| ≤ 2 * (X : ℝ) := him.trans hT.2
    obtain ⟨ha, hb⟩ := abs_le.mp h2
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · have hf := Int.floor_le ρ.im
      have : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ (((2 * X + 1 : ℕ) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hfib : ∀ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
      ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖ ≤
        12 * A * Real.log X / m * (1 / (|(k : ℝ)| + 1)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkR : |(k : ℝ)| ≤ 2 * (X : ℝ) + 1 := by
      rw [abs_le]
      constructor
      · have : ((-((2 * X + 1 : ℕ) : ℤ) : ℤ) : ℝ) ≤ k := by exact_mod_cast hk.1
        push_cast at this; linarith
      · have : ((k : ℤ) : ℝ) ≤ (((2 * X + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hk.2
        push_cast at this; linarith
    have hwin : ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) ≤
        A * Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) := by
      apply hA q χ ((k : ℝ) + 1 / 2)
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h0, h1, _⟩ := (hZset ρ).mp hρ.1
      refine ⟨hz, h0, h1, ?_⟩
      have e1 := Int.floor_le ρ.im
      have e2 := Int.lt_floor_add_one ρ.im
      rw [hρ.2] at e1 e2
      rw [abs_le]; constructor <;> linarith
    have hlogq : Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) ≤ 4 * Real.log X := by
      have habs : |(k : ℝ) + 1 / 2| ≤ 2 * (X : ℝ) + 2 := by
        have := abs_le.mp hkR
        rw [abs_le]; constructor <;> linarith
      have hle : (q : ℝ) * (|(k : ℝ) + 1 / 2| + 2) ≤ (X : ℝ) ^ 4 := by
        calc (q : ℝ) * (|(k : ℝ) + 1 / 2| + 2) ≤ (X : ℝ) * (2 * (X : ℝ) + 4) :=
              mul_le_mul hqX (by linarith) (by positivity) (by positivity)
          _ ≤ (X : ℝ) * (X : ℝ) ^ 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (X : ℝ) ^ 4 := by ring
      calc Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) ≤ Real.log ((X : ℝ) ^ 4) :=
            Real.log_le_log (mul_pos (by linarith) (by positivity)) hle
        _ = 4 * Real.log X := by rw [Real.log_pow]; norm_num
    have hterm : ∀ ρ ∈ Z.filter (fun ρ => ⌊ρ.im⌋ = k),
        (mult χ ρ : ℝ) / ‖ρ‖ ≤ (mult χ ρ : ℝ) * ((3 / m) / (|(k : ℝ)| + 1)) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hn := hmX ρ hρ.1
      have him : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
      have e1 := Int.floor_le ρ.im
      have e2 := Int.lt_floor_add_one ρ.im
      rw [hρ.2] at e1 e2
      have hk1 : |(k : ℝ)| ≤ |ρ.im| + 1 := by
        have := le_abs_self ρ.im
        have := neg_abs_le ρ.im
        rw [abs_le]; constructor <;> linarith
      have hρ0 : 0 < ‖ρ‖ := lt_of_lt_of_le hm0 hn
      -- `|k| + 1 ≤ ‖ρ‖ + 2 ≤ 3 ‖ρ‖ / m`
      have hkey : (|(k : ℝ)| + 1) * m ≤ 3 * ‖ρ‖ := by
        have : (|(k : ℝ)| + 1) ≤ ‖ρ‖ + 2 := by linarith
        nlinarith [abs_nonneg (k : ℝ)]
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [inv_eq_one_div, div_div, div_le_div_iff₀ hρ0 (by positivity)]
      linarith
    have hpos : (0 : ℝ) ≤ (3 / m) / (|(k : ℝ)| + 1) := by positivity
    calc ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖
        ≤ ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) * ((3 / m) / (|(k : ℝ)| + 1)) :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ)) * ((3 / m) / (|(k : ℝ)| + 1)) := by
          rw [Finset.sum_mul]
      _ ≤ (A * (4 * Real.log X)) * ((3 / m) / (|(k : ℝ)| + 1)) :=
          mul_le_mul_of_nonneg_right
            (hwin.trans (mul_le_mul_of_nonneg_left hlogq hA0)) hpos
      _ = 12 * A * Real.log X / m * (1 / (|(k : ℝ)| + 1)) := by ring
  have hharm : 2 * (1 + Real.log (((2 * X + 1 : ℕ) : ℝ) + 1)) ≤ 10 * Real.log X := by
    have hle : (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ (X : ℝ) ^ 3 := by push_cast; linarith
    have : Real.log (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ 3 * Real.log X := by
      calc Real.log (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ Real.log ((X : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) hle
        _ = 3 * Real.log X := by rw [Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hbud := log_sq_power_budget508 hX1 hε2
  have hinvm : 1 / m = (1 / c) * (X : ℝ) ^ (ε / 2) := by
    rw [hm, Real.rpow_neg hXp.le]
    field_simp
  have hsplitX : (X : ℝ) ^ (ε / 2) * (X : ℝ) ^ (ε / 2) = (X : ℝ) ^ ε := by
    rw [← Real.rpow_add hXp]; ring_nf
  calc ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖
      = ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
          ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖ :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
          12 * A * Real.log X / m * (1 / (|(k : ℝ)| + 1)) := Finset.sum_le_sum hfib
    _ = 12 * A * Real.log X / m *
          ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
            1 / (|(k : ℝ)| + 1) := by rw [Finset.mul_sum]
    _ ≤ 12 * A * Real.log X / m * (10 * Real.log X) :=
        mul_le_mul_of_nonneg_left ((int_abs_harmonic_feed508 (2 * X + 1)).trans hharm)
          (by positivity)
    _ = 120 * A * (1 / m) * Real.log X ^ 2 := by ring
    _ = 120 * A / c * (X : ℝ) ^ (ε / 2) * Real.log X ^ 2 := by rw [hinvm]; ring
    _ ≤ 120 * A / c * (X : ℝ) ^ (ε / 2) * ((2 / (ε / 2)) ^ 2 * (X : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left hbud (by positivity)
    _ = 120 * A / c * (2 / (ε / 2)) ^ 2 * ((X : ℝ) ^ (ε / 2) * (X : ℝ) ^ (ε / 2)) := by ring
    _ = 120 * A / c * (2 / (ε / 2)) ^ 2 * (X : ℝ) ^ ε := by rw [hsplitX]

end LeanLab.BhowmikGrimmelt2026
