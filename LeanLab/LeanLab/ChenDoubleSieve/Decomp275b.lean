import LeanLab.ChenDoubleSieve.Decomp275a
import LeanLab.ChenDoubleSieve.Decomp275d
import LeanLab.ChenDoubleSieve.FunctionalStatements
import LeanLab.ChenDoubleSieve.Wu2008Lemma22Sum

/-!
Wu 2004 Section 10 at its printed parameter choice.
The open leaves separate weights, sieve estimates, and numerical integration.
Source: https://arxiv.org/pdf/0705.1652, pages 34 to 42.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task275
open Wu41 (S PS)
open Wu08Sum (P2 P4)
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The prime difference sequence used in Sections 9 and 10. -/
def primeSequence (N : ℕ) : Finset ℕ :=
  ((range (N + 1)).filter Nat.Prime).image (fun p => N - p)

/-- Section 10's fixed kappa one. -/
def kappa1 : ℝ := 1 / 12
/-- Section 10's fixed kappa two. -/
def kappa2 : ℝ := 29 / 250
/-- Section 10's fixed sigma one. -/
def sigma1 : ℝ := 41 / 125
/-- Section 10's fixed sigma two. -/
def sigma2 : ℝ := 141 / 500

/-- The printed parameters satisfy equation 10.1 and the Lemma 9.2 constraint. -/
theorem parameters_admissible :
    kappa1 < kappa2 ∧ kappa2 ≤ 1 / 8 ∧ (1 / 4 : ℝ) < sigma2 ∧
      sigma2 < sigma1 ∧ sigma1 < 1 / 3 ∧ 1 < 3 * sigma1 + kappa1 ∧
      1 < 2 * sigma1 + sigma2 + kappa2 ∧ 3 * kappa1 + 1 / 4 = 1 / 2 := by
  norm_num [kappa1, kappa2, sigma1, sigma2]

/-- Every Buchstab argument in the F13 integral exceeds three and a half. -/
theorem fourfold13_argument (t1 t2 t3 t4 : ℝ) (ht2 : 0 < t2)
    (h1 : t1 ≤ kappa2) (h2 : t2 ≤ kappa2) (h3 : t3 ≤ kappa2)
    (h4 : t4 ≤ kappa2) :
    (3.5 : ℝ) ≤ (1 - t1 - t2 - t3 - t4) / t2 := by
  rw [le_div_iff₀ ht2]
  norm_num [kappa2] at *
  linarith

/-- Every Buchstab argument in the F14 integral exceeds three and a half. -/
theorem fourfold14_argument (t1 t2 t3 t4 : ℝ) (ht2 : 0 < t2)
    (h1 : t1 ≤ kappa2) (h2 : t2 ≤ kappa2)
    (h4 : t4 ≤ 1 / 2 - 2 * kappa1 - t3) :
    (3.5 : ℝ) ≤ (1 - t1 - t2 - t3 - t4) / t2 := by
  rw [le_div_iff₀ ht2]
  norm_num [kappa1, kappa2] at *
  linarith

/-- The twelve coefficients in the final display on page 42.
The order is 0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 14. -/
def weighted (v : Fin 12 → ℝ) : ℝ :=
  4 * v 0 - v 1 - v 2 - v 3 + v 4 + v 5 -
    2 * v 6 - 2 * v 7 - v 8 - v 9 - v 10 - v 11

/-- The twelve actual sieve counts retained from Lemma 9.2.
For Upsilon 13 and 14 the modulus excludes p one as in the intended reading
already used for the analogous sums elsewhere in this folder. -/
def sieveTerms (N : ℕ) : Fin 12 → ℝ :=
  let A := primeSequence N
  let y := fun k : ℝ => (N : ℝ) ^ k
  ![(S A 1 N (y kappa1) : ℝ),
    (∑ p ∈ PS N (y kappa1) (y kappa2), S A p N p : ℕ),
    (∑ p ∈ PS N (y kappa1) (y sigma1), S A p N (y kappa1) : ℕ),
    (∑ p ∈ PS N (y kappa1) (y sigma2), S A p N (y kappa1) : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < y kappa2),
      S A (q.1 * q.2) N (y kappa1) : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ (p : ℝ) < y kappa2 ∧
      y kappa2 ≤ q ∧ (q : ℝ) < y (1 / 2 - 2 * kappa1) / p),
      S A (q.1 * q.2) N (y kappa1) : ℕ),
    (∑ q ∈ P2 N (fun p q => y sigma1 ≤ p ∧ p < q ∧
      (q : ℝ) < Real.sqrt ((N : ℝ) / p)), S A (q.1 * q.2) (N * q.1) q.2 : ℕ),
    (∑ q ∈ P2 N (fun p q => y sigma2 ≤ p ∧ p < q ∧
      (q : ℝ) < Real.sqrt ((N : ℝ) / p)), S A (q.1 * q.2) (N * q.1) q.2 : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ (p : ℝ) < y sigma1 ∧
      y sigma1 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      S A (q.1 * q.2) (N * q.1) q.2 : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa2 ≤ p ∧ (p : ℝ) < y sigma2 ∧
      y sigma2 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      S A (q.1 * q.2) (N * q.1) (y sigma1) : ℕ),
    (∑ q ∈ P4 N (fun p q r s => y kappa1 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧
      (s : ℝ) < y kappa2),
      S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℕ),
    (∑ q ∈ P4 N (fun p q r s => y kappa1 ≤ p ∧ p < q ∧ q < r ∧
      (r : ℝ) < y kappa2 ∧ y kappa2 ≤ s ∧
      (s : ℝ) < y (1 / 2 - 2 * kappa1) / r),
      S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℕ)]

/-- The fourfold Buchstab integral common to F13 and F14 in equation 10.12.
The upper endpoint for t four distinguishes the two terms. -/
def fourfold (ω : ℝ → ℝ) (last : ℝ → ℝ) (a b : ℝ) (lower weight : ℝ → ℝ) : ℝ :=
  ∫ t1 in a..b,
    (∫ t2 in t1..kappa2,
      (∫ t3 in t2..kappa2,
        (∫ t4 in lower t3..last t3,
          ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3) / t2 ^ 2) /
      weight t1

/-- F0 to F14 from equations 10.2 to 10.12, in the order used by sieveTerms. -/
def integralTerms (F f ω : ℝ → ℝ) : Fin 12 → ℝ :=
  let eg := exp eulerMascheroniConstant
  ![2 * f (1 / (2 * kappa1)) / (kappa1 * eg),
    4 / eg * ∫ t in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1), F t,
    4 / eg * ∫ t in ((1 / 2 - sigma1) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t),
    4 / eg * ∫ t in ((1 / 2 - sigma2) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t),
    2 / (kappa1 * eg) * ∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t,
    2 / (kappa1 * eg) * ∫ t in kappa1..kappa2,
      (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
        f ((1 / 2 - t - u) / kappa1) / u) / t,
    8 * ∫ t in (2 : ℝ)..(1 / sigma1 - 1), log (t - 1) / t,
    8 * ∫ t in (2 : ℝ)..(1 / sigma2 - 1), log (t - 1) / t,
    36 / 5 * (∫ t in kappa1..(1 / 10 : ℝ),
      log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t) ^ 2)) +
      8 * ∫ t in (1 / 10 : ℝ)..sigma1,
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t)),
    8 * ∫ t in kappa2..sigma2,
      log (1 / sigma2 - 1 - t / sigma2) / (t * (1 - t)),
    36 / 5 * fourfold ω (fun _ => kappa2) kappa1 (1 / 10) id (fun t => t * (1 - t)) +
      8 * fourfold ω (fun _ => kappa2) (1 / 10) kappa2 id id,
    36 / 5 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) kappa1 (1 / 10) (fun _ => kappa2) (fun t => t * (1 - t)) +
      8 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) (1 / 10) kappa2 (fun _ => kappa2) id]

/-! ### Existence of the standard functions
The delay equation of Wu 2004 equation 2.6 is solved by the method of steps in
`DelaySolver` below. -/

namespace DelaySolver
open Set MeasureTheory intervalIntegral Filter
open scoped Topology

set_option maxHeartbeats 4000000 in
/-- One-layer existence for the scalar delay equation `X' u = k u * X (u - 1)`.
`X` is produced on `Icc 1 (N + 2)` with the integral form of the equation. -/
private theorem delay_layer_exists (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Ici (2 : ℝ)))
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc (1 : ℝ) 2)) :
    ∀ N : ℕ, ∃ X : ℝ → ℝ,
      ContinuousOn X (Set.Icc (1 : ℝ) ((N : ℝ) + 2)) ∧
      (∀ u ∈ Set.Icc (1 : ℝ) (2 : ℝ), X u = φ u) ∧
      (∀ u ∈ Set.Icc (2 : ℝ) ((N : ℝ) + 2), X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) := by
  intro N
  induction N with
  | zero =>
    have h2 : (((0 : ℕ) : ℝ) + 2) = (2 : ℝ) := by norm_num
    refine ⟨fun u => if u ≤ (2 : ℝ) then φ u else 0, ?_, ?_, ?_⟩
    · rw [h2]
      exact (continuousOn_congr (fun u hu => by simp [hu.2])).mpr hφ
    · intro u hu
      simp [hu.2]
    · intro u hu
      rw [h2] at hu
      have hu2 : u = 2 := le_antisymm hu.2 hu.1
      subst hu2
      simp
  | succ n ih =>
    obtain ⟨X, hcont, hφX, heq⟩ := ih
    have hidx : ((((n + 1 : ℕ)) : ℝ) + 2) = (n : ℝ) + 2 + 1 := by push_cast; ring
    have hc1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hc2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hc3 : (n : ℝ) + 2 ≤ (n : ℝ) + 2 + 1 := by norm_num
    have hfcont : ∀ a b : ℝ, 2 ≤ a → b ≤ (n : ℝ) + 2 + 1 →
        ContinuousOn (fun t : ℝ => k t * X (t - 1)) (Set.Icc a b) := by
      intro a b ha hb
      have hk' : ContinuousOn k (Set.Icc a b) := by
        refine hk.mono ?_
        intro x hx
        simp only [Set.mem_Ici]
        linarith [hx.1]
      have hXc : ContinuousOn (fun t : ℝ => X (t - 1)) (Set.Icc a b) := by
        refine hcont.comp (continuous_id.sub continuous_const).continuousOn ?_
        intro t ht
        simp only [Set.mem_Icc]
        constructor
        · linarith [ht.1]
        · linarith [ht.2]
      exact hk'.mul hXc
    have hub : ∀ a b : ℝ, a ≤ b → 2 ≤ a → b ≤ (n : ℝ) + 2 + 1 →
        ContinuousOn (fun t : ℝ => k t * X (t - 1)) (uIcc a b) := by
      intro a b hab ha hb
      rw [uIcc_of_le hab]
      exact hfcont a b ha hb
    set X' : ℝ → ℝ := fun u =>
      if u ≤ (n : ℝ) + 2 then X u
      else X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1) with hX'
    have hstep : ∀ u : ℝ, X' u = if u ≤ (n : ℝ) + 2 then X u
        else X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1) :=
      fun u => congrFun hX' u
    refine ⟨X', ?_, ?_, ?_⟩
    · rw [hidx]
      have hun : Set.Icc (1 : ℝ) ((n : ℝ) + 2) ∪ Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 2 + 1) =
          Set.Icc (1 : ℝ) ((n : ℝ) + 2 + 1) := Icc_union_Icc_eq_Icc hc1 hc3
      rw [← hun]
      refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
      · refine hcont.congr ?_
        intro u hu
        rw [hstep, if_pos hu.2]
      · have hint : IntegrableOn (fun t : ℝ => k t * X (t - 1))
            (uIcc ((n : ℝ) + 2) ((n : ℝ) + 2 + 1)) :=
          (hub _ _ hc3 hc2 le_rfl).integrableOn_compact isCompact_uIcc
        have hprim : ContinuousOn
            (fun u => X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1))
            (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 2 + 1)) := by
          have h := (continuousOn_const (c := X ((n : ℝ) + 2))).add
            (continuousOn_primitive_interval hint)
          rwa [uIcc_of_le hc3] at h
        refine hprim.congr ?_
        intro u hu
        rw [hstep]
        by_cases h : u ≤ (n : ℝ) + 2
        · rw [if_pos h]
          have hue : u = (n : ℝ) + 2 := le_antisymm h hu.1
          subst hue
          simp
        · rw [if_neg h]
    · intro u hu
      have hu2 : u ≤ (n : ℝ) + 2 := by linarith [hu.2, hc2]
      rw [hstep, if_pos hu2]
      exact hφX u hu
    · rw [hidx]
      intro u hu
      have hX'2 : X' 2 = X 2 := by
        rw [hstep, if_pos hc2]
      rw [hX'2]
      by_cases h : u ≤ (n : ℝ) + 2
      · have hX'u : X' u = X u := by
          rw [hstep, if_pos h]
        rw [hX'u, heq u ⟨hu.1, h⟩]
        congr 1
        refine integral_congr (fun t ht => ?_)
        rw [uIcc_of_le hu.1] at ht
        have hle : t - 1 ≤ (n : ℝ) + 2 := by linarith [ht.2]
        rw [hstep, if_pos hle]
      · have hX'u : X' u = X ((n : ℝ) + 2) + ∫ t in ((n : ℝ) + 2)..u, k t * X (t - 1) := by
          rw [hstep, if_neg h]
        rw [hX'u, heq ((n : ℝ) + 2) ⟨hc2, le_rfl⟩, add_assoc]
        have hleu : u ≤ (n : ℝ) + 2 + 1 := hu.2
        have hAB : IntervalIntegrable (fun t : ℝ => k t * X (t - 1)) volume (2 : ℝ)
            ((n : ℝ) + 2) :=
          (hub 2 ((n : ℝ) + 2) (by linarith) (by norm_num) (by linarith)).intervalIntegrable
        have hBC : IntervalIntegrable (fun t : ℝ => k t * X (t - 1)) volume ((n : ℝ) + 2) u :=
          (hub ((n : ℝ) + 2) u (le_of_not_ge h) hc2 hleu).intervalIntegrable
        rw [integral_add_adjacent_intervals hAB hBC]
        congr 1
        refine integral_congr (fun t ht => ?_)
        rw [uIcc_of_le hu.1] at ht
        have hle : t - 1 ≤ (n : ℝ) + 2 := by linarith [ht.2]
        rw [hstep, if_pos hle]

set_option maxHeartbeats 4000000 in
/-- Global existence for the scalar delay equation `X' u = k u * X (u - 1)`
with prescribed values on `[1, 2]`. -/
private theorem delay_exists (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Ici (2 : ℝ)))
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc (1 : ℝ) 2)) :
    ∃ X : ℝ → ℝ, ContinuousOn X (Set.Ici (1 : ℝ)) ∧
      (∀ u ∈ Set.Icc (1 : ℝ) 2, X u = φ u) ∧
      (∀ u : ℝ, 2 ≤ u → X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) := by
  classical
  have hex : ∀ N : ℕ, ∃ X : ℝ → ℝ,
      ContinuousOn X (Set.Icc (1 : ℝ) ((N : ℝ) + 2)) ∧
      (∀ u ∈ Set.Icc (1 : ℝ) (2 : ℝ), X u = φ u) ∧
      (∀ u ∈ Set.Icc (2 : ℝ) ((N : ℝ) + 2),
        X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) :=
    delay_layer_exists k hk φ hφ
  -- two layer solutions agree on the common interval
  have agree : ∀ (N M : ℕ) (X Y : ℝ → ℝ),
      (∀ u ∈ Set.Icc (1 : ℝ) 2, X u = φ u) →
      (∀ u ∈ Set.Icc (2 : ℝ) ((N : ℝ) + 2),
        X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1)) →
      (∀ u ∈ Set.Icc (1 : ℝ) 2, Y u = φ u) →
      (∀ u ∈ Set.Icc (2 : ℝ) ((M : ℝ) + 2),
        Y u = Y 2 + ∫ t in (2 : ℝ)..u, k t * Y (t - 1)) →
      ∀ u ∈ Set.Icc (1 : ℝ) (((min N M : ℕ) : ℝ) + 2), X u = Y u := by
    intro N M X Y hXφ hXe hYφ hYe
    have key : ∀ n : ℕ, n ≤ N → n ≤ M → ∀ u ∈ Set.Icc (1 : ℝ) ((n : ℝ) + 2), X u = Y u := by
      intro n
      induction n with
      | zero =>
        intro _ _ u hu
        have hu2 : u ≤ 2 := by
          simpa using hu.2
        rw [hXφ u ⟨hu.1, hu2⟩, hYφ u ⟨hu.1, hu2⟩]
      | succ n ih =>
        intro hnN hnM u hu
        have hidx : (((n + 1 : ℕ)) : ℝ) + 2 = (n : ℝ) + 2 + 1 := by push_cast; ring
        rw [hidx] at hu
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        by_cases h : u ≤ (n : ℝ) + 2
        · exact ih (by omega) (by omega) u ⟨hu.1, h⟩
        · have hgt : (n : ℝ) + 2 < u := not_le.mp h
          have hu2 : (2 : ℝ) ≤ u := by linarith
          have hcast : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
          have hcastM : ((n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
          have huN : u ≤ (N : ℝ) + 2 := by push_cast at hcast; linarith [hu.2]
          have huM : u ≤ (M : ℝ) + 2 := by push_cast at hcastM; linarith [hu.2]
          rw [hXe u ⟨hu2, huN⟩, hYe u ⟨hu2, huM⟩]
          congr 1
          · exact ih (by omega) (by omega) 2 ⟨by norm_num, by linarith⟩
          · refine integral_congr (fun t ht => ?_)
            rw [uIcc_of_le hu2] at ht
            have ht1 : (1 : ℝ) ≤ t - 1 := by linarith [ht.1]
            have ht2 : t - 1 ≤ (n : ℝ) + 2 := by linarith [ht.2, hu.2]
            rw [ih (by omega) (by omega) (t - 1) ⟨ht1, ht2⟩]
    intro u hu
    refine key (min N M) (min_le_left _ _) (min_le_right _ _) u ⟨hu.1, ?_⟩
    rw [Nat.cast_min] at hu ⊢
    rcases le_total (N : ℝ) (M : ℝ) with h | h
    · rw [min_eq_left h] at hu ⊢
      exact hu.2
    · rw [min_eq_right h] at hu ⊢
      exact hu.2
  choose Xc hXc using hex
  -- the index of the layer used at a point
  set Nf : ℝ → ℕ := fun u => max 1 ⌈u⌉₊ with hNfdef
  have hNfbig : ∀ u : ℝ, u ≤ (Nf u : ℝ) + 2 := by
    intro u
    have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have h2 : (⌈u⌉₊ : ℝ) ≤ (Nf u : ℝ) := by
      rw [hNfdef]
      exact_mod_cast le_max_right 1 ⌈u⌉₊
    linarith
  set X : ℝ → ℝ := fun u => Xc (Nf u) u with hXdef
  have hXval : ∀ v : ℝ, X v = Xc (Nf v) v := fun v => congrFun hXdef v
  have hXeq : ∀ (N M : ℕ) (u : ℝ), u ∈ Set.Icc (1 : ℝ) (((min N M : ℕ) : ℝ) + 2) →
      Xc N u = Xc M u :=
    fun N M u hu => agree N M (Xc N) (Xc M) (hXc N).2.1 (hXc N).2.2 (hXc M).2.1 (hXc M).2.2 u hu
  have hmem : ∀ (N M : ℕ) (u : ℝ), 1 ≤ u → u ≤ (N : ℝ) + 2 → u ≤ (M : ℝ) + 2 →
      u ∈ Set.Icc (1 : ℝ) (((min N M : ℕ) : ℝ) + 2) := by
    intro N M u h1 hN hM
    refine ⟨h1, ?_⟩
    rw [Nat.cast_min]
    rcases le_total (N : ℝ) (M : ℝ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hφX : ∀ u ∈ Set.Icc (1 : ℝ) 2, X u = φ u := by
    intro u hu
    rw [hXval]
    exact (hXc (Nf u)).2.1 u hu
  have hXint : ∀ u : ℝ, 2 ≤ u → X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1) := by
    intro u hu
    have hstep := (hXc (Nf u)).2.2 u ⟨hu, hNfbig u⟩
    rw [hXval, hstep]
    congr 1
    · rw [hXval]
      exact hXeq (Nf u) (Nf 2) 2
        (hmem _ _ 2 (by norm_num) (by linarith [hNfbig u]) (hNfbig 2))
    · refine integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hu] at ht
      have ht1 : (1 : ℝ) ≤ t - 1 := by linarith [ht.1]
      have htle : t - 1 ≤ (Nf u : ℝ) + 2 := by linarith [ht.2, hNfbig u]
      rw [hXval]
      rw [hXeq (Nf u) (Nf (t - 1)) (t - 1) (hmem _ _ _ ht1 htle (hNfbig (t - 1)))]
  have hcontIcc : ∀ n : ℕ, ContinuousOn X (Set.Icc (1 : ℝ) ((n : ℝ) + 2)) := by
    intro n
    refine ((hXc n).1).congr ?_
    intro u hu
    rw [hXval]
    exact hXeq (Nf u) n u (hmem _ _ _ hu.1 (hNfbig u) hu.2)
  have hcont : ContinuousOn X (Set.Ici (1 : ℝ)) := by
    intro u hu
    obtain ⟨n, hn⟩ := exists_nat_gt u
    have hun : Set.Icc (1 : ℝ) ((n : ℝ) + 2) ∪ Set.Ioi ((n : ℝ) + 2) = Set.Ici (1 : ℝ) := by
      ext x
      simp only [mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · rintro (⟨h1, _⟩ | h)
        · exact h1
        · linarith
      · intro hx
        by_cases h : x ≤ (n : ℝ) + 2
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (not_le.mp h)
    rw [← hun]
    refine ContinuousWithinAt.union (hcontIcc n u ⟨hu, by linarith⟩) ?_
    refine continuousWithinAt_of_notMem_closure ?_
    simp only [closure_Ioi, Set.mem_Ici]
    linarith
  exact ⟨X, hcont, hφX, hXint⟩

set_option maxHeartbeats 1000000 in
/-- Derivative form of the delay equation. -/
private theorem delay_hasDerivAt (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Ici (2 : ℝ)))
    (X : ℝ → ℝ) (hX : ContinuousOn X (Set.Ici (1 : ℝ)))
    (hint : ∀ u : ℝ, 2 ≤ u → X u = X 2 + ∫ t in (2 : ℝ)..u, k t * X (t - 1))
    {u : ℝ} (hu : 2 < u) : HasDerivAt X (k u * X (u - 1)) u := by
  have hfcont : ContinuousOn (fun t : ℝ => k t * X (t - 1)) (Set.Ici (2 : ℝ)) := by
    intro x hx
    have h1 : ContinuousWithinAt k (Set.Ici (2 : ℝ)) x := hk x hx
    have h2 : ContinuousWithinAt (fun t : ℝ => X (t - 1)) (Set.Ici (2 : ℝ)) x := by
      have hx2 : (2 : ℝ) ≤ x := hx
      refine ContinuousWithinAt.comp (hX (x - 1) (by simp only [Set.mem_Ici]; linarith))
        (continuous_id.sub continuous_const).continuousWithinAt ?_
      intro t ht
      simp only [Set.mem_Ici] at ht ⊢
      linarith
    exact h1.mul h2
  have hcont2 : ContinuousOn (fun t : ℝ => k t * X (t - 1)) (uIcc (2 : ℝ) u) := by
    rw [uIcc_of_le (le_of_lt hu)]
    exact hfcont.mono (fun x hx => hx.1)
  have hInt : IntervalIntegrable (fun t : ℝ => k t * X (t - 1)) volume (2 : ℝ) u :=
    hcont2.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => k t * X (t - 1)) (𝓝 u) :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hfcont.mono (fun x hx => le_of_lt hx))) u (by simpa only [Set.mem_Ioi] using hu)
  have hfu : ContinuousAt (fun t : ℝ => k t * X (t - 1)) u :=
    hfcont.continuousAt (Ici_mem_nhds hu)
  have h1 : HasDerivAt (fun v : ℝ => ∫ t in (2 : ℝ)..v, k t * X (t - 1))
      (k u * X (u - 1)) u := intervalIntegral.integral_hasDerivAt_right hInt hmeas hfu
  have h2 : HasDerivAt (fun v : ℝ => X 2 + ∫ t in (2 : ℝ)..v, k t * X (t - 1))
      (k u * X (u - 1)) u := h1.const_add (X 2)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact hint v hv.le

set_option maxHeartbeats 1000000 in
/-- Buchstab's function exists (Wu 2004 Lemma 2.10). -/
private theorem exists_buchstab : ∃ ω : ℝ → ℝ, IsBuchstab ω := by
  have hk : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.Ici (2 : ℝ)) := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx
    have hx1 : (1 : ℝ) < x := by linarith
    have hden : (0 : ℝ) < x - 1 := by linarith
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (ne_of_gt hden)).continuousWithinAt
  obtain ⟨X, hXc, hXφ, hXint⟩ :=
    delay_exists (fun t : ℝ => 1 / (t - 1)) hk (fun _ => 1) continuousOn_const
  refine ⟨fun u => X u / u, ?_, ?_, ?_⟩
  · refine hXc.div continuousOn_id ?_
    intro u hu
    have hu1 : (1 : ℝ) ≤ u := hu
    exact ne_of_gt (by linarith)
  · intro u h1 h2
    change X u / u = 1 / u
    rw [hXφ u ⟨h1, h2⟩]
  · intro u hu
    have hderiv : HasDerivAt X (1 / (u - 1) * X (u - 1)) u :=
      delay_hasDerivAt (fun t : ℝ => 1 / (t - 1)) hk X hXc hXint hu
    have hval : (fun v : ℝ => v * (X v / v)) =ᶠ[𝓝 u] X := by
      filter_upwards [isOpen_ne.mem_nhds (show u ≠ 0 by linarith)] with v hv
      field_simp
    have hd : HasDerivAt X (X (u - 1) / (u - 1)) u := by
      convert hderiv using 1
      field_simp
    exact hd.congr_of_eventuallyEq hval

set_option maxHeartbeats 2000000 in
/-- The linear sieve pair exists (Wu 2004 equation 2.6). -/
private theorem exists_linear_sieve : ∃ F f : ℝ → ℝ, IsLinearSieve F f := by
  have hk1 : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.Ici (2 : ℝ)) := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx
    have hden : (0 : ℝ) < x - 1 := by linarith
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (ne_of_gt hden)).continuousWithinAt
  have hk2 : ContinuousOn (fun t : ℝ => -(1 / (t - 1))) (Set.Ici (2 : ℝ)) := hk1.neg
  have hφ : ContinuousOn (fun _ : ℝ => 2 * exp eulerMascheroniConstant) (Set.Icc (1 : ℝ) 2) :=
    continuousOn_const
  obtain ⟨P, hPc, hPφ, hPint⟩ :=
    delay_exists (fun t : ℝ => 1 / (t - 1)) hk1 _ hφ
  obtain ⟨M, hMc, hMφ, hMint⟩ :=
    delay_exists (fun t : ℝ => -(1 / (t - 1))) hk2 _ hφ
  have hPderiv : ∀ u : ℝ, 2 < u → HasDerivAt P (P (u - 1) / (u - 1)) u := by
    intro u hu
    have h := delay_hasDerivAt (fun t : ℝ => 1 / (t - 1)) hk1 P hPc hPint hu
    convert h using 1
    field_simp
  have hMderiv : ∀ u : ℝ, 2 < u → HasDerivAt M (-(M (u - 1) / (u - 1))) u := by
    intro u hu
    have h := delay_hasDerivAt (fun t : ℝ => -(1 / (t - 1))) hk2 M hMc hMint hu
    convert h using 1
    field_simp
  set Pe : ℝ → ℝ := fun u => P (max u 1) with hPe
  set Me : ℝ → ℝ := fun u => M (max u 1) with hMe
  have hPec : Continuous Pe :=
    hPc.comp_continuous (by fun_prop) (fun u => by
      simp only [Set.mem_Ici]; exact le_max_right _ _)
  have hMec : Continuous Me :=
    hMc.comp_continuous (by fun_prop) (fun u => by
      simp only [Set.mem_Ici]; exact le_max_right _ _)
  set G : ℝ → ℝ := fun u => (Pe u + Me u) / 2 with hG
  set g : ℝ → ℝ := fun u => (Pe u - Me u) / 2 with hg
  have hPv : ∀ u ∈ Set.Icc (0 : ℝ) 2, Pe u = 2 * exp eulerMascheroniConstant := by
    intro u hu
    simp only [hPe]
    exact hPφ (max u 1) ⟨le_max_right _ _, max_le hu.2 (by norm_num)⟩
  have hMv : ∀ u ∈ Set.Icc (0 : ℝ) 2, Me u = 2 * exp eulerMascheroniConstant := by
    intro u hu
    simp only [hMe]
    exact hMφ (max u 1) ⟨le_max_right _ _, max_le hu.2 (by norm_num)⟩
  refine ⟨fun u => G u / u, fun u => g u / u, ?_, ?_, ?_, ?_⟩
  · -- continuity of `F`
    exact (hPec.add hMec).div_const 2 |>.continuousOn.div continuousOn_id
      (fun u hu => ne_of_gt hu)
  · -- continuity of `f`
    exact (hPec.sub hMec).div_const 2 |>.continuousOn.div continuousOn_id
      (fun u hu => ne_of_gt hu)
  · -- the initial values
    intro u hu1 hu2
    have hPu := hPv u ⟨le_of_lt hu1, hu2⟩
    have hMu := hMv u ⟨le_of_lt hu1, hu2⟩
    constructor
    · show G u / u = 2 * exp eulerMascheroniConstant / u
      rw [hG]
      simp only [hPu, hMu]
      field_simp
      norm_num
    · show g u / u = 0
      rw [hg]
      simp only [hPu, hMu]
      ring
  · -- the differential relations
    intro u hu
    have h1gt : (1 : ℝ) < u := by linarith
    have hPeq : Pe =ᶠ[𝓝 u] P := by
      filter_upwards [Ioi_mem_nhds h1gt] with v hv
      simp only [hPe]
      rw [max_eq_left (le_of_lt hv)]
    have hMeq : Me =ᶠ[𝓝 u] M := by
      filter_upwards [Ioi_mem_nhds h1gt] with v hv
      simp only [hMe]
      rw [max_eq_left (le_of_lt hv)]
    have hP1 : Pe (u - 1) = P (u - 1) := by
      simp only [hPe]
      rw [max_eq_left (by linarith : (1 : ℝ) ≤ u - 1)]
    have hM1 : Me (u - 1) = M (u - 1) := by
      simp only [hMe]
      rw [max_eq_left (by linarith : (1 : ℝ) ≤ u - 1)]
    have hPed : HasDerivAt Pe (P (u - 1) / (u - 1)) u :=
      (hPderiv u hu).congr_of_eventuallyEq hPeq
    have hMed : HasDerivAt Me (-(M (u - 1) / (u - 1))) u :=
      (hMderiv u hu).congr_of_eventuallyEq hMeq
    have hGfun : (fun v : ℝ => (Pe v + Me v) / 2) = G := by rw [hG]
    have hgfun : (fun v : ℝ => (Pe v - Me v) / 2) = g := by rw [hg]
    constructor
    · dsimp only
      have h0 : HasDerivAt (fun v : ℝ => (Pe v + Me v) / 2)
          ((P (u - 1) / (u - 1) + -(M (u - 1) / (u - 1))) / 2) u :=
        (hPed.add hMed).div_const 2
      have hGd : HasDerivAt G
          ((P (u - 1) / (u - 1) - M (u - 1) / (u - 1)) / 2) u := by
        have h1 := hGfun ▸ h0
        have hval : (P (u - 1) / (u - 1) + -(M (u - 1) / (u - 1))) / 2 =
            (P (u - 1) / (u - 1) - M (u - 1) / (u - 1)) / 2 := by ring
        rwa [hval] at h1
      have hval : (fun v : ℝ => v * (G v / v)) =ᶠ[𝓝 u] G := by
        filter_upwards [isOpen_ne.mem_nhds (show u ≠ 0 by linarith)] with v hv
        field_simp
      have hgoal : g (u - 1) / (u - 1) =
          (P (u - 1) / (u - 1) - M (u - 1) / (u - 1)) / 2 := by
        show (Pe (u - 1) - Me (u - 1)) / 2 / (u - 1) = _
        rw [hP1, hM1]
        field_simp
      rw [hgoal]
      exact hGd.congr_of_eventuallyEq hval
    · dsimp only
      have h0 : HasDerivAt (fun v : ℝ => (Pe v - Me v) / 2)
          ((P (u - 1) / (u - 1) - -(M (u - 1) / (u - 1))) / 2) u :=
        (hPed.sub hMed).div_const 2
      have hgd : HasDerivAt g
          ((P (u - 1) / (u - 1) + (M (u - 1) / (u - 1))) / 2) u := by
        have h1 := hgfun ▸ h0
        have hval : (P (u - 1) / (u - 1) - -(M (u - 1) / (u - 1))) / 2 =
            (P (u - 1) / (u - 1) + M (u - 1) / (u - 1)) / 2 := by ring
        rwa [hval] at h1
      have hval : (fun v : ℝ => v * (g v / v)) =ᶠ[𝓝 u] g := by
        filter_upwards [isOpen_ne.mem_nhds (show u ≠ 0 by linarith)] with v hv
        field_simp
      have hgoal : G (u - 1) / (u - 1) =
          (P (u - 1) / (u - 1) + M (u - 1) / (u - 1)) / 2 := by
        show (Pe (u - 1) + Me (u - 1)) / 2 / (u - 1) = _
        rw [hP1, hM1]
        field_simp
      rw [hgoal]
      exact hgd.congr_of_eventuallyEq hval

end DelaySolver

/-- LEAF. Wu 2004 page 6 equation 2.6 and page 9 Lemma 2.10.
The standard linear sieve pair and Buchstab function exist. -/
theorem standard_functions : ∃ F f ω : ℝ → ℝ, IsLinearSieve F f ∧ IsBuchstab ω := by
  obtain ⟨F, f, hF⟩ := DelaySolver.exists_linear_sieve
  obtain ⟨ω, hω⟩ := DelaySolver.exists_buchstab
  exact ⟨F, f, ω, hF, hω⟩

/-- LEAF. Wu 2004 pages 34 to 37 equation 9.4, specialized to page 42's parameters.
Drop the four nonnegative terms and retain the stated power remainder. -/
theorem weighted_sieve_power : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      weighted (sieveTerms N) ≤ 4 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  sorry

/-- Absorb the remainder with the proved elementary normalization theorem.
CONDITIONAL ON weighted_sieve_power only. -/
theorem weighted_sieve : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      weighted (sieveTerms N) - ε * Θ N ≤ 4 * (D12 N : ℝ) := by
  intro ε hε
  obtain ⟨C, hC, M, hM⟩ := weighted_sieve_power
  obtain ⟨K, hK⟩ := power_remainder_absorbed C ε hC hε
  refine ⟨max M K, ?_⟩
  intro N hEven hN
  have hw := hM N hEven ((le_max_left M K).trans hN)
  have he := hK N ((le_max_right M K).trans hN)
  linarith

/-- LEAF. Wu 2004 pages 38 and 39 equations 10.2 and 10.5.
The three positively weighted terms have their printed lower estimates. -/
theorem positive_estimates (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 ∧
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 ∧
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  sorry

/-- LEAF. Wu 2004 pages 39 to 41 equations 10.3, 10.4, 10.10 to 10.12.
The nine negatively weighted terms have their printed upper estimates. -/
theorem negative_estimates (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  sorry

/-- LEAF. Wu 2004 page 42 final display of Section 10.
This bounds actual integrals, rather than comparing equal rational constants. -/
theorem integral_evaluation (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    (3344307 : ℝ) / 4000000 ≤ weighted (integralTerms F f ω) / 4 := by
  sorry

/-- Componentwise bounds lose seventeen epsilon units in the weighted sum. -/
theorem weighted_comparison (v w : Fin 12 → ℝ) (t ε : ℝ)
    (hp : ∀ i : Fin 12, i ∈ ({0, 4, 5} : Finset (Fin 12)) → (v i - ε) * t ≤ w i)
    (hn : ∀ i : Fin 12, i ∈ ({1, 2, 3, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)) →
      w i ≤ (v i + ε) * t) :
    weighted v * t - 17 * ε * t ≤ weighted w := by
  have h0 := hp 0 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h1 := hn 1 (by decide)
  have h2 := hn 2 (by decide)
  have h3 := hn 3 (by decide)
  have h6 := hn 6 (by decide)
  have h7 := hn 7 (by decide)
  have h8 := hn 8 (by decide)
  have h9 := hn 9 (by decide)
  have h10 := hn 10 (by decide)
  have h11 := hn 11 (by decide)
  dsimp only [weighted]
  linarith

/-- The exact statement of thm2_analytic_link follows from the five open leaves.
Its rational hypothesis carries no information about the integrals. -/
theorem thm2_analytic_link_checked (h : (83607 : ℝ) / 100000 ≤ 0.83607) :
    ChenLower 0.836 := by
  obtain ⟨F, f, ω, hF, hω⟩ := standard_functions
  obtain ⟨Nw, hw⟩ := weighted_sieve (1 / 1000000) (by norm_num)
  obtain ⟨Np, hp⟩ := positive_estimates F f ω hF hω (1 / 1000000) (by norm_num)
  obtain ⟨Nn, hn⟩ := negative_estimates F f ω hF hω (1 / 1000000) (by norm_num)
  have heval := integral_evaluation F f ω hF hω
  refine ⟨max Nw (max Np Nn), ?_⟩
  intro N hEven hN
  have hwN := hw N hEven (by omega)
  have hpN := hp N hEven (by omega)
  have hnN := hn N hEven (by omega)
  have hpositive : ∀ i : Fin 12, i ∈ ({0, 4, 5} : Finset (Fin 12)) →
      (integralTerms F f ω i - 1 / 1000000) * Θ N ≤ sieveTerms N i := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpN.1
    · exact hpN.2.1
    · exact hpN.2.2
  have hcomb := weighted_comparison (integralTerms F f ω) (sieveTerms N)
    (Θ N) (1 / 1000000) hpositive hnN
  have hscaled := mul_le_mul_of_nonneg_right heval (Θ_nonneg N)
  have ht := Θ_nonneg N
  nlinarith only [hwN, hcomb, hscaled, ht]

end LeanLab.ChenDoubleSieve.Task275
