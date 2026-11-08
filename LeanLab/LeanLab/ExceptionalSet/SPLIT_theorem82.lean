/-
Split of `theorem82` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026` into two leaves.

`theorem82` says: for `δ ∈ (0, 1)` there is `c > 0` such that for every `A > 5/2`, every large
`r` and `X = r^A`, the almost-all multiples hypothesis `HL84 r δ X` rules out a real zero
`β > 1 - c / log X` of a primitive real character modulo `r`. The page-32 argument of the module
has two deferred steps; everything else it needs is already proved there (`dichotomy`,
`exists_good_multiple`, `Sing_pos`, `sq_eq_one_of_dirichlet_neg_one`, and the assembly
`theorem82_of_prop81`, all proved there with no open input):

* LEAF 1, the analytic step: at such a zero, `r₂(N)` has the shape `(1 + χ(-1) b) 𝔖(N) N + E`
  with `|b - 1| < 3δ/4` and `|E| ≤ (δ/4) 𝔖(N) N`, for every even multiple `N` of `r` in `[X/2, X]`
  outside an exceptional set `B` of at most `X^{3/5}` values.
* LEAF 2, the counting step: for `A > 5/2` and `r` large the even multiples of `r` in `[X/2, X]`
  outnumber `2 X^{3/5}`, so `B` and the `X^{3/5}` lost values still leave a multiple behind.

`theorem82_split` is the statement of `theorem82`, character for character, assembled from those
two leaves with no `sorry` and without `theorem82`. Each leaf is strictly easier than the whole:
the first drops the pigeonhole and the negation of the zero, the second drops all analysis. Both
leaves are OPEN; the assembly compiles with them open.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.BhowmikGrimmelt2026

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction

noncomputable section

/-- LEAF 1 of 2, the analytic step. Let `δ ∈ (0, 1)`, let `χ` be a primitive real character
modulo `r` with a real zero `β ∈ (1 - c / log X, 1)`, and let `X = r ^ A` with `A > 5/2`. Then
there is a set `B` of at most `X^{3/5}` values such that at every even multiple `N` of `r` in
`[X/2, X]` outside `B` the sum `r₂(N) = ∑_{n₁+n₂=N} Λ n₁ Λ n₂` equals
`(1 + χ(-1) b) 𝔖(N) N + E` with a shift `|b - 1| < 3δ/4` and an error `|E| ≤ (δ/4) 𝔖(N) N`.

The constant `1` in the bound on `B` normalises the size of the exceptional set; only that the
bound is a fixed multiple of `X^{3/5}` matters below, and the count in LEAF 2 absorbs twice it.
Nothing is asserted about the zero, about `HL84`, or about `N` inside `B`. -/
theorem leaf_expansion_off_exceptional_set :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ,
      ∀ (r : ℕ) [NeZero r], r0 ≤ r → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
        (∀ a, (χ a).im = 0) →
        (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧
          DirichletCharacter.LFunction χ β = 0) →
        ∃ B : Finset ℕ, (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) ∧
          ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
            |E| ≤ δ / 4 * (Sing N * N) ∧
            r2 N = (1 + (χ (-1)).re * b) * (Sing N * N) + E := by
  sorry

/-- The even multiples of `r` in `[X/2, X]` number at least `X/(4r) - 1`: the map
`k ↦ 2rk` is injective and lands in `evenMult r X` for `k ∈ [⌈X/(4r)⌉, ⌊X/(2r)⌋]`. -/
private theorem evenMult_card_ge (r : ℕ) (hr : 1 ≤ r) (X : ℝ) (hX : 0 ≤ X) :
    X / (4 * (r : ℝ)) - 1 ≤ ((evenMult r X).card : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  set c : ℕ := ⌈X / (4 * (r : ℝ))⌉₊ with hcv
  set d : ℕ := ⌊X / (2 * (r : ℝ))⌋₊ with hdv
  have hX2 : (0:ℝ) ≤ X / (2 * (r:ℝ)) := by positivity
  have hX4 : (0:ℝ) ≤ X / (4 * (r:ℝ)) := by positivity
  have hquarter : X / (4 * (r:ℝ)) ≤ X / (2 * (r:ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) hX
  have hinj : Function.Injective (fun k : ℕ => 2 * r * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * r) hab
  have hsub : (Finset.Icc c d).image (fun k => 2 * r * k) ⊆ evenMult r X := by
    intro N hN
    simp only [Finset.mem_image, Finset.mem_Icc] at hN
    obtain ⟨k, ⟨hkc, hkd⟩, rfl⟩ := hN
    simp only [evenMult, Finset.mem_filter, Finset.mem_Icc]
    have hc' : X / (4 * (r:ℝ)) ≤ (c:ℝ) := Nat.le_ceil _
    have hck : (c:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkc
    have hd'' : (d:ℝ) ≤ X / (2*(r:ℝ)) := Nat.floor_le hX2
    have hkd' : (k:ℝ) ≤ (d:ℝ) := by exact_mod_cast hkd
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Nat.ceil_le]
      have hkey : X / 2 ≤ 2 * (r:ℝ) * (k:ℝ) := by
        have h : X / 2 = 2 * (r:ℝ) * (X / (4 * (r:ℝ))) := by field_simp <;> ring
        rw [h]
        have hmono : (r:ℝ) * (X / (4 * (r:ℝ))) ≤ (r:ℝ) * (k:ℝ) :=
          mul_le_mul_of_nonneg_left (le_trans hc' hck) hr0.le
        nlinarith
      simpa using hkey
    · refine Nat.le_floor ?_
      have hkk : (k:ℝ) ≤ X / (2*(r:ℝ)) := le_trans hkd' hd''
      have hkey : (2:ℝ) * (r:ℝ) * (k:ℝ) ≤ X := by
        have h : (2:ℝ)*(r:ℝ)*(X / (2*(r:ℝ))) = X := by field_simp <;> ring
        calc (2:ℝ)*(r:ℝ)*(k:ℝ) ≤ (2:ℝ)*(r:ℝ)*(X/(2*(r:ℝ))) :=
              mul_le_mul_of_nonneg_left hkk (by positivity)
          _ = X := h
      simpa using hkey
    · exact ⟨r * k, by ring⟩
    · exact ⟨2 * k, by ring⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc] at hcard
  have hdc : c ≤ d + 1 := by
    refine Nat.ceil_le.mpr ?_
    have hlt : X / (4 * (r:ℝ)) < (d:ℝ) + 1 := by
      have hfr : X / (2*(r:ℝ)) < (d:ℝ) + 1 := Nat.lt_floor_add_one _
      linarith
    simpa [Nat.cast_add, Nat.cast_one] using hlt.le
  have hcast : ((d + 1 - c : ℕ) : ℝ) = (d:ℝ) + 1 - (c:ℝ) := by
    rw [Nat.cast_sub hdc, Nat.cast_add, Nat.cast_one]
  have hcardR : ((d + 1 - c : ℕ) : ℝ) ≤ ((evenMult r X).card : ℝ) := by exact_mod_cast hcard
  rw [hcast] at hcardR
  have hlt : (d:ℝ) + 1 - (c:ℝ) > X / (4 * (r:ℝ)) - 1 := by
    have hd' : X / (2*(r:ℝ)) < (d:ℝ) + 1 := Nat.lt_floor_add_one _
    have hc' : (c:ℝ) < X / (4*(r:ℝ)) + 1 := Nat.ceil_lt_add_one hX4
    have hrx : X / (2*(r:ℝ)) = 2 * (X / (4*(r:ℝ))) := by field_simp <;> ring
    linarith
  linarith

/-- LEAF 2 of 2, the counting step: for `X = r ^ A` with `A > 5/2` and `r` large, the even
multiples of `r` in `[X/2, X]` outnumber `2 X^{3/5}`.

This is where the exponent threshold `5/2` comes from: the count grows like `X / r = r^{A-1}`,
while `X^{3/5} = r^{3A/5}`, and `A - 1 > 3A/5` exactly when `A > 5/2`, so the ratio tends to
infinity in `r` for each fixed `A > 5/2`. The order of the quantifiers is the statement's own:
`r0` comes after `A` and does depend on it. A single `r0` for all `A > 5/2` does not exist, since
at `A = 5/2 + ε` the inequality needs `r^{2ε/5} > 4`, so `r0 → ∞` as `ε → 0`. No analysis is
asserted here. -/
theorem leaf_even_multiples_dominate_exceptions :
    ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
      2 * (((r : ℝ) ^ A) ^ (3 / 5 : ℝ)) < ((evenMult r ((r : ℝ) ^ A)).card : ℝ) := by

  intro A hA
  have he : 0 < 2 / 5 * A - 1 := by linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((16 : ℝ) ^ (1 / (2 / 5 * A - 1)))
  refine ⟨max m 2, ?_⟩
  intro r _ hr
  have hr2 : 2 ≤ r := le_trans (le_max_right _ _) hr
  have hrm : m ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by positivity
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    have : (1:ℝ) ≤ 2 := by norm_num
    calc (1:ℝ) ≤ 2 := this
      _ ≤ (r:ℝ) := by exact_mod_cast hr2
  -- the key growth fact: `r^(2A/5-1) > 16`
  have hpow : (16 : ℝ) < (r : ℝ) ^ (2 / 5 * A - 1) := by
    have hle : ((m : ℝ)) ≤ (r : ℝ) := by exact_mod_cast hrm
    have hcancel : ((16 : ℝ) ^ (1 / (2 / 5 * A - 1))) ^ (2 / 5 * A - 1) = 16 := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16)]
      have h1 : 1 / (2 / 5 * A - 1) * (2 / 5 * A - 1) = 1 := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt he)]
      rw [h1, Real.rpow_one]
    have hstep : ((16 : ℝ) ^ (1 / (2 / 5 * A - 1))) ^ (2 / 5 * A - 1)
        < (r : ℝ) ^ (2 / 5 * A - 1) :=
      Real.rpow_lt_rpow (by positivity) (lt_of_lt_of_le hm hle) he
    rw [hcancel] at hstep
    exact hstep
  -- `u = r^(3A/5) ≥ 1`
  have hu1 : (1:ℝ) ≤ (r : ℝ) ^ (A * (3 / 5)) :=
    Real.one_le_rpow hr1 (by nlinarith)
  have hu0 : (0:ℝ) < (r : ℝ) ^ (A * (3 / 5)) := lt_of_lt_of_le zero_lt_one hu1
  -- `r^(A-1) = u * r^(2A/5-1)`
  have hV : (r : ℝ) ^ (A - 1) = (r : ℝ) ^ (A * (3 / 5)) * (r : ℝ) ^ (2 / 5 * A - 1) := by
    rw [← Real.rpow_add hr0]
    congr 1
    ring
  have hVbig : 8 * (r : ℝ) ^ (A * (3 / 5)) + 4 < (r : ℝ) ^ (A - 1) := by
    have hvu : 16 * (r : ℝ) ^ (A * (3 / 5))
        < (r : ℝ) ^ (A * (3 / 5)) * (r : ℝ) ^ (2 / 5 * A - 1) := by
      rw [mul_comm ((r : ℝ) ^ (A * (3 / 5)))]
      exact mul_lt_mul_of_pos_right hpow hu0
    rw [← hV] at hvu
    nlinarith [hvu, hu1]
  -- `(r^A)^(3/5) = u`
  have hX35 : ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) = (r : ℝ) ^ (A * (3 / 5)) := by
    rw [← Real.rpow_mul hr0.le]
  -- `r^A / (4r) = r^(A-1) / 4`
  have hXAr : (r : ℝ) ^ A = (r : ℝ) ^ (A - 1) * (r : ℝ) := by
    nth_rewrite 1 [show A = (A - 1) + 1 by ring]
    rw [Real.rpow_add hr0, Real.rpow_one]
  have hXdiv : (r : ℝ) ^ A / (4 * (r : ℝ)) = (r : ℝ) ^ (A - 1) / 4 := by
    rw [hXAr, mul_div_mul_right _ _ (ne_of_gt hr0)]
  have hXpos : (0:ℝ) < (r : ℝ) ^ A := Real.rpow_pos_of_pos hr0 A
  have hcard := evenMult_card_ge r (by omega) ((r : ℝ) ^ A) hXpos.le
  rw [hXdiv] at hcard
  rw [hX35]
  linarith

/-- `theorem82` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026`, assembled from the two leaves:
the exceptional set of LEAF 1 and the two extra multiples of LEAF 2 leave an even multiple `N` of
`r` in `[X/2, X]` outside `B` at which `HL84` holds, and `dichotomy` refutes `HL84` there for the
sign `χ(-1) = ±1`. -/
theorem theorem82_split : Theorem82 := by
  have h81 : Prop81AtMultiples := by
    intro δ hδ hδ1
    obtain ⟨c, hc, hstep⟩ := leaf_expansion_off_exceptional_set δ hδ hδ1
    refine ⟨c, hc, fun A hA => ?_⟩
    obtain ⟨ra, hra⟩ := hstep A hA
    obtain ⟨rc, hrc⟩ := leaf_even_multiples_dominate_exceptions A hA
    refine ⟨max ra rc, fun r _ hr χ hprim hreal hzero => ?_⟩
    have hra' : ra ≤ r := le_trans (le_max_left _ _) hr
    have hrc' : rc ≤ r := le_trans (le_max_right _ _) hr
    obtain ⟨B, hBcard, hBN⟩ := hra r hra' χ hprim hreal hzero
    have hcount : 2 * (((r : ℝ) ^ A) ^ (3 / 5 : ℝ)) < ((evenMult r ((r : ℝ) ^ A)).card : ℝ) :=
      hrc r hrc'
    refine ⟨B, by linarith, fun N hN hNB => hBN N hN hNB⟩
  exact theorem82_of_prop81 h81

-- Axiom audit driver for the assembly.
#print axioms theorem82_split

end

end LeanLab.ExceptionalSet.BG2026
