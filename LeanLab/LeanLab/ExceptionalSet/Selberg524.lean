import LeanLab.ExceptionalSet.Selberg524Trig
import LeanLab.ExceptionalSet.Selberg524Ineq
import LeanLab.ExceptionalSet.Selberg524Coeff
import LeanLab.ExceptionalSet.Selberg524Expand
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
Selberg's cosine majorant of a centred arc, assembled from the four helper files.

With `N = H + 1` and `k = ⌈N w / 2⌉`, the trigonometric polynomial
`T θ = (2 k + 1) / N + ∑ h, G h cos (2 π h θ)` is nonnegative everywhere and at least one
on `[-k / N, k / N]`, which contains `[-w / 2, w / 2]`.  Away from the grid nodes this is the
closed form of the helper files; at the nodes it follows by continuity.
-/

namespace LeanLab.ExceptionalSet.Selberg524

open Real Finset

private lemma sin_sq_node524 (H : ℕ) (θ : ℝ) (i k : ℕ) :
    sin (π * (((H : ℝ) + 1) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) ^ 2 =
      sin (π * (((H : ℝ) + 1) * θ)) ^ 2 := by
  have hN : ((H : ℝ) + 1) ≠ 0 := by positivity
  have e0 : ((H : ℝ) + 1) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)) =
      ((H : ℝ) + 1) * θ - ((i : ℝ) - (k : ℝ)) := by
    field_simp
  have e : 2 * (π * (((H : ℝ) + 1) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) =
      2 * (π * (((H : ℝ) + 1) * θ)) - (((i : ℤ) - (k : ℤ) : ℤ) : ℝ) * (2 * π) := by
    rw [e0]
    push_cast
    ring
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub, e, Real.cos_sub_int_mul_two_pi]

private lemma node_ne524 (H : ℕ) (θ : ℝ) (hs : sin (π * (((H : ℝ) + 1) * θ)) ≠ 0) (i k : ℕ) :
    sin (π * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))) ≠ 0 := by
  intro h0
  have e := fejer_closed524 H (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))
  rw [h0, sin_sq_node524] at e
  have h2 : sin (π * (((H : ℝ) + 1) * θ)) ^ 2 = 0 := by
    rw [← e]
    ring
  exact hs (by simpa using h2)

private lemma node_plus524 (H k : ℕ) (θ : ℝ) :
    θ - (((0 : ℕ) : ℝ) - (k : ℝ)) / ((H : ℝ) + 1) = θ + (k : ℝ) / ((H : ℝ) + 1) := by
  push_cast
  ring

private lemma node_minus524 (H k : ℕ) (θ : ℝ) :
    θ - (((2 * k : ℕ) : ℝ) - (k : ℝ)) / ((H : ℝ) + 1) = θ - (k : ℝ) / ((H : ℝ) + 1) := by
  push_cast
  ring

private lemma phi_node524 (H : ℕ) (θ : ℝ) (hs : sin (π * (((H : ℝ) + 1) * θ)) ≠ 0) (i k : ℕ) :
    ((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) *
        cos (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) =
      sin (π * (((H : ℝ) + 1) * θ)) ^ 2 *
        (1 / sin (π * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))) ^ 2) := by
  have h0 := node_ne524 H θ hs i k
  have e := fejer_closed524 H (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))
  rw [sin_sq_node524] at e
  have h1 : sin (π * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))) ^ 2 ≠ 0 := pow_ne_zero 2 h0
  rw [mul_one_div]
  exact eq_div_of_mul_eq h1 ((mul_comm _ _).trans e)

private lemma psi_node524 (H : ℕ) (θ : ℝ) (hs : sin (π * (((H : ℝ) + 1) * θ)) ≠ 0) (i k : ℕ) :
    ∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) =
      sin (π * (((H : ℝ) + 1) * θ)) ^ 2 *
          (cos (π * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))) /
            sin (π * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) -
        sin (2 * π * (((H : ℝ) + 1) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) / 2 := by
  have h0 := node_ne524 H θ hs i k
  have e := conj_closed524 H (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))
  rw [sin_sq_node524] at e
  have e2 := eq_div_of_mul_eq h0 ((mul_comm _ _).trans e)
  rw [← mul_div_assoc]
  linarith

private lemma S_eq524 (H k : ℕ) (θ : ℝ) :
    sin (2 * π * (((H : ℝ) + 1) * (θ + (k : ℝ) / ((H : ℝ) + 1)))) =
      sin (2 * π * (((H : ℝ) + 1) * (θ - (k : ℝ) / ((H : ℝ) + 1)))) := by
  have hN : ((H : ℝ) + 1) ≠ 0 := by positivity
  have a1 : ((H : ℝ) + 1) * (θ + (k : ℝ) / ((H : ℝ) + 1)) = ((H : ℝ) + 1) * θ + (k : ℝ) := by
    field_simp
  have a2 : ((H : ℝ) + 1) * (θ - (k : ℝ) / ((H : ℝ) + 1)) = ((H : ℝ) + 1) * θ - (k : ℝ) := by
    field_simp
  have e : 2 * π * (((H : ℝ) + 1) * θ + (k : ℝ)) =
      2 * π * (((H : ℝ) + 1) * θ - (k : ℝ)) + ((2 * k : ℕ) : ℝ) * (2 * π) := by
    push_cast
    ring
  rw [a1, a2, e, Real.sin_add_nat_mul_two_pi]

/-- Nonnegativity of the closed form away from the grid nodes. -/
private lemma R_nonneg524 (H k : ℕ) (θ : ℝ) (hs : sin (π * (((H : ℝ) + 1) * θ)) ≠ 0) :
    0 ≤ (1 / ((H : ℝ) + 1) ^ 2) *
          ∑ i ∈ range (2 * k + 1),
            (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) *
              cos (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))))) +
        (1 / (π * ((H : ℝ) + 1))) *
          (∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ + (k : ℝ) / ((H : ℝ) + 1)))) -
            ∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ - (k : ℝ) / ((H : ℝ) + 1))))) := by
  have hN : (1 : ℝ) ≤ (H : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) H]
  have hp := psi_node524 H θ hs 0 k
  have hm := psi_node524 H θ hs (2 * k) k
  rw [node_plus524] at hp
  rw [node_minus524] at hm
  have hS := S_eq524 H k θ
  have hsum := Finset.sum_congr rfl
    (fun i (_ : i ∈ range (2 * k + 1)) => phi_node524 H θ hs i k)
  rw [← Finset.mul_sum] at hsum
  have hB := selberg_nonneg524 ((H : ℝ) + 1) hN k θ (fun i _ => node_ne524 H θ hs i k)
  have hs2 : 0 ≤ sin (π * (((H : ℝ) + 1) * θ)) ^ 2 := sq_nonneg _
  rw [hsum, hp, hm, hS]
  linear_combination mul_nonneg hs2 hB

/-- The closed form is at least one inside the arc, away from the grid nodes. -/
private lemma R_ge_one524 (H k : ℕ) (hk : 2 * k + 2 ≤ H + 1) (θ : ℝ)
    (hs : sin (π * (((H : ℝ) + 1) * θ)) ≠ 0)
    (h1 : -((k : ℝ) / ((H : ℝ) + 1)) < θ) (h2 : θ < (k : ℝ) / ((H : ℝ) + 1)) :
    1 ≤ (1 / ((H : ℝ) + 1) ^ 2) *
          ∑ i ∈ range (2 * k + 1),
            (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) *
              cos (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))))) +
        (1 / (π * ((H : ℝ) + 1))) *
          (∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ + (k : ℝ) / ((H : ℝ) + 1)))) -
            ∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ - (k : ℝ) / ((H : ℝ) + 1))))) := by
  have hN0 : ((H : ℝ) + 1) ≠ 0 := by positivity
  have hp := psi_node524 H θ hs 0 k
  have hm := psi_node524 H θ hs (2 * k) k
  rw [node_plus524] at hp
  rw [node_minus524] at hm
  have hS := S_eq524 H k θ
  have hM := selberg_ge_one524 (H + 1) k hk θ
    (by simpa only [Nat.cast_add, Nat.cast_one] using h1)
    (by simpa only [Nat.cast_add, Nat.cast_one] using h2)
  simp only [Nat.cast_add, Nat.cast_one] at hM
  have harg : ∀ i : ℕ, θ + (k : ℝ) / ((H : ℝ) + 1) - (i : ℝ) / ((H : ℝ) + 1) =
      θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1) := fun i => by ring
  have hg := fejer_grid_sum524 H (θ + (k : ℝ) / ((H : ℝ) + 1))
  simp only [harg] at hg
  rw [← Finset.sum_range_add_sum_Ico _ (show 2 * k + 1 ≤ H + 1 by omega)] at hg
  have hI := Finset.sum_congr rfl
    (fun i (_ : i ∈ Ico (2 * k + 1) (H + 1)) => phi_node524 H θ hs i k)
  rw [← Finset.mul_sum] at hI
  rw [hI] at hg
  have hs2 : 0 ≤ sin (π * (((H : ℝ) + 1) * θ)) ^ 2 := sq_nonneg _
  have h3 := mul_le_mul_of_nonneg_left hM hs2
  have hNN : (1 / ((H : ℝ) + 1) ^ 2) * ((H : ℝ) + 1) ^ 2 = 1 := by field_simp
  rw [hp, hm, hS]
  linear_combination h3 - (1 / ((H : ℝ) + 1) ^ 2) * hg - hNN

/-- A continuous function that is at least `c` at the non-nodes just to the right of `θ₀`
is at least `c` at `θ₀`. -/
private lemma ge_of_right524 (T : ℝ → ℝ) (hT : Continuous T) (c N : ℝ) (hN : 0 < N)
    (θ₀ b : ℝ) (hb : θ₀ < b)
    (h : ∀ θ, θ₀ < θ → θ < b → sin (π * (N * θ)) ≠ 0 → c ≤ T θ) : c ≤ T θ₀ := by
  have hfl : θ₀ < (((⌊N * θ₀⌋ : ℤ) : ℝ) + 1) / N := by
    rw [lt_div_iff₀ hN]
    linarith [Int.lt_floor_add_one (N * θ₀)]
  have hlt : θ₀ < min b ((((⌊N * θ₀⌋ : ℤ) : ℝ) + 1) / N) := lt_min hb hfl
  refine ge_of_tendsto ((hT.tendsto θ₀).mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hlt) ?_)
  intro θ hθ
  obtain ⟨h1, h2⟩ := hθ
  have h3 := lt_of_lt_of_le h2 (min_le_left _ _)
  have h4 := lt_of_lt_of_le h2 (min_le_right _ _)
  refine h θ h1 h3 ?_
  intro h0
  rw [Real.sin_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  have hn' : (n : ℝ) = N * θ := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    rw [hn]
    ring
  have h5 : θ * N < ((⌊N * θ₀⌋ : ℤ) : ℝ) + 1 := (lt_div_iff₀ hN).mp h4
  have h6 : N * θ₀ < N * θ := mul_lt_mul_of_pos_left h1 hN
  have h7 : ((⌊N * θ₀⌋ : ℤ) : ℝ) ≤ N * θ₀ := Int.floor_le _
  have a : ((⌊N * θ₀⌋ : ℤ) : ℝ) < (n : ℝ) := by rw [hn']; linarith
  have b' : (n : ℝ) < ((⌊N * θ₀⌋ : ℤ) : ℝ) + 1 := by rw [hn']; linarith
  have a' : ⌊N * θ₀⌋ < n := by exact_mod_cast a
  have b'' : n < ⌊N * θ₀⌋ + 1 := by exact_mod_cast b'
  omega

private lemma final_aux524 (H k : ℕ) (hk0 : 0 < k) (T : ℝ → ℝ) (hT : Continuous T)
    (heven : ∀ θ, T (-θ) = T θ)
    (hnn : ∀ θ, sin (π * (((H : ℝ) + 1) * θ)) ≠ 0 → 0 ≤ T θ)
    (hge : ∀ θ, sin (π * (((H : ℝ) + 1) * θ)) ≠ 0 → -((k : ℝ) / ((H : ℝ) + 1)) < θ →
      θ < (k : ℝ) / ((H : ℝ) + 1) → 1 ≤ T θ) (θ : ℝ) :
    0 ≤ T θ ∧ (|θ| ≤ (k : ℝ) / ((H : ℝ) + 1) → 1 ≤ T θ) := by
  have hN : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  constructor
  · exact ge_of_right524 T hT 0 ((H : ℝ) + 1) hN θ (θ + 1) (by linarith)
      (fun θ' _ _ hs => hnn θ' hs)
  · intro habs
    obtain ⟨ha, hb⟩ := abs_le.mp habs
    have key : ∀ θ₀ : ℝ, -((k : ℝ) / ((H : ℝ) + 1)) ≤ θ₀ → θ₀ < (k : ℝ) / ((H : ℝ) + 1) →
        1 ≤ T θ₀ := fun θ₀ h1 h2 =>
      ge_of_right524 T hT 1 ((H : ℝ) + 1) hN θ₀ ((k : ℝ) / ((H : ℝ) + 1)) h2
        (fun θ' h3 h4 hs => hge θ' hs (by linarith) h4)
    have hkpos : 0 < (k : ℝ) / ((H : ℝ) + 1) := div_pos (Nat.cast_pos.mpr hk0) hN
    rcases lt_or_eq_of_le hb with h | h
    · exact key θ ha h
    · rw [← heven θ]
      apply key
      · linarith
      · linarith

/-- Selberg's polynomial for the arc `[-k / N, k / N]`, `N = H + 1`: nonnegative everywhere
and at least one on the arc. -/
theorem selberg_T524 (H k : ℕ) (hk0 : 0 < k) (hk : 2 * k + 2 ≤ H + 1) (θ : ℝ) :
    0 ≤ (2 * (k : ℝ) + 1) / ((H : ℝ) + 1) +
        ∑ h ∈ Icc 1 H,
          (2 * (((H : ℝ) + 1) - (h : ℝ)) / ((H : ℝ) + 1) ^ 2 *
              ∑ i ∈ range (2 * k + 1),
                cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) +
            2 / (π * ((H : ℝ) + 1)) * sin (2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))))) *
          cos (2 * π * ((h : ℝ) * θ)) ∧
    (|θ| ≤ (k : ℝ) / ((H : ℝ) + 1) →
      1 ≤ (2 * (k : ℝ) + 1) / ((H : ℝ) + 1) +
        ∑ h ∈ Icc 1 H,
          (2 * (((H : ℝ) + 1) - (h : ℝ)) / ((H : ℝ) + 1) ^ 2 *
              ∑ i ∈ range (2 * k + 1),
                cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) +
            2 / (π * ((H : ℝ) + 1)) * sin (2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))))) *
          cos (2 * π * ((h : ℝ) * θ))) := by
  have hTR := fun θ : ℝ => selberg_expand524 H k θ
  refine final_aux524 H k hk0
    (fun θ : ℝ => (2 * (k : ℝ) + 1) / ((H : ℝ) + 1) +
        ∑ h ∈ Icc 1 H,
          (2 * (((H : ℝ) + 1) - (h : ℝ)) / ((H : ℝ) + 1) ^ 2 *
              ∑ i ∈ range (2 * k + 1),
                cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) +
            2 / (π * ((H : ℝ) + 1)) * sin (2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))))) *
          cos (2 * π * ((h : ℝ) * θ))) ?_ ?_ ?_ ?_ θ
  · exact continuous_const.add (continuous_finsetSum _ fun h _ => by fun_prop)
  · intro θ
    simp only [mul_neg, Real.cos_neg]
  · intro θ hs
    exact le_of_le_of_eq (R_nonneg524 H k θ hs) (hTR θ).symm
  · intro θ hs h1 h2
    exact le_of_le_of_eq (R_ge_one524 H k hk θ hs h1 h2) (hTR θ).symm

theorem selberg_cosine_majorant524 (w : ℝ) (H : ℕ) (hw0 : 0 < w) (hC : w + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ g : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |g h| ≤ 4 / (h : ℝ)) ∧
      ∀ θ : ℝ, (if |θ| ≤ w / 2 then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * θ)) := by
  have hN : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have hCN : ((H : ℝ) + 1) * w + 4 < (H : ℝ) + 1 := by
    have h4 : 4 / ((H : ℝ) + 1) < 1 - w := by linarith
    have := (div_lt_iff₀ hN).mp h4
    linarith
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, ((H : ℝ) + 1) * w / 2 ≤ (k : ℝ) ∧
      (k : ℝ) < ((H : ℝ) + 1) * w / 2 + 1 :=
    ⟨⌈((H : ℝ) + 1) * w / 2⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩
  have hNw : 0 < ((H : ℝ) + 1) * w := mul_pos hN hw0
  have hk0 : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast this
  have hkN : 2 * k + 2 ≤ H + 1 := by
    have : ((2 * k + 2 : ℕ) : ℝ) < ((H + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h' : 2 * k + 2 < H + 1 := by exact_mod_cast this
    omega
  have hwk : w / 2 ≤ (k : ℝ) / ((H : ℝ) + 1) := by
    rw [le_div_iff₀ hN]
    linarith
  refine ⟨(2 * (k : ℝ) + 1) / ((H : ℝ) + 1), fun h =>
    2 * (((H : ℝ) + 1) - (h : ℝ)) / ((H : ℝ) + 1) ^ 2 *
        ∑ i ∈ range (2 * k + 1),
          cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) +
      2 / (π * ((H : ℝ) + 1)) * sin (2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1)))),
    ?_, ?_, ?_⟩
  · have e : w + 4 / ((H : ℝ) + 1) = (w * ((H : ℝ) + 1) + 4) / ((H : ℝ) + 1) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hN.le
  · intro h hh
    have hh' := Finset.mem_Icc.mp hh
    exact selberg_coeff_bound524 H k h hh'.1 hh'.2
  · intro θ
    obtain ⟨hnn, hge⟩ := selberg_T524 H k hk0 hkN θ
    split_ifs with hθ
    · exact hge (le_trans hθ hwk)
    · exact hnn

end LeanLab.ExceptionalSet.Selberg524
