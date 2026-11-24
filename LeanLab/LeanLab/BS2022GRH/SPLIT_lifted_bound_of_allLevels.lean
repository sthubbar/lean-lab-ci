/-
Split of the LEAF `lifted_bound_of_allLevels` of SPLIT_fixedKappa_of_allLevels into two leaves,
with an assembly that has the leaf's statement verbatim and uses no sorry.

The leaf holds steps 1 to 7 of the U-1611 hand proof of `fixedKappa_of_allLevels`, in the doc comment
of that theorem in SieveAllLevels1611, plus one use of `LinearSieveAllLevels`. The split separates:

Leaf A, HARD, steps 1 to 6: for each δ there is a lifted system at z' = exp(M (1 + εF) log z),
D' = (D(1 - δ))^M, whose new primes outside Q' lie above a level y₀ with log z' ≤ K log y₀, with
density at most (1 + η)/p', and with S' = S, X' = X, R' ≤ Rκ.
Leaf B, HARD, step 7: any system whose primes outside Q' lie above a large y₀, with log z' ≤ K log y₀
and density at most (1 + η)/p for small η, satisfies `AllLevelsPremise` with ε. This is explicit
Mertens on all primes of a range.

The assembly applies `LinearSieveAllLevels` once at z', D' and checks, PROVED here, that the level
log D' / log z' equals sδ for every M and that the conditions z' ≤ D', z'² ≤ D', 2 ≤ z' hold.
The lifted system is not a new definition: Leaf A states its existence, with the sieve quantities of
the lifted system written out exactly as `LinearSieveAllLevels` writes them.

This file adds no definition, changes no existing file, and leaves the sealed statements untouched.
The assembly declares neither the parent nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_fixedKappa_of_allLevels

namespace LeanLab.BS2022GRH.SieveAllLevels1611
open Real Finset Classical Filter Topology
open LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH

/-- LEAF: steps 1 to 6 of the hand proof of `fixedKappa_of_allLevels`: blocks B_i of new primes with
g'(p') = c_i/p', c_i → 1 by Mertens; lifts q' ≥ q^M of Q; image mass a'; S' = S, X' = X and
R' ≤ Rκ by `block_kappa_le` and `size_lift`. K = W_k + 1, y₀ the least new prime outside Q'.
HARD: Mertens on the primes of a range and the construction of the new integers. Strictly easier
than the parent: no sieve, no all levels premise. Non-vacuity: the system of
`fixedPremise_instance` meets every hypothesis. -/
theorem lift_exists {εF : ℝ} :
  ∀ (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ),
    (∀ n, 0 ≤ a n) → (∀ n, n ∉ supp → a n = 0) → (∀ p ∈ P, p.Prime) → (↑Q ⊆ P) →
    (∀ q ∈ Q, (q : ℝ) < z) → (∀ p ∈ P, 0 < g p ∧ g p < 1) →
    0 < εF → 2 ≤ z →
    FixedPremise P Q g εF z →
    let Pz := (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ (p : ℝ) < z)
    let S := ∑ n ∈ supp.filter (fun n => ∀ p ∈ Pz, ¬ p ∣ n), a n
    let X := ∑ n ∈ supp, a n * ∏ p ∈ Pz, (1 - g p)
    let r := fun d : ℕ => (∑ n ∈ supp.filter (fun n => d ∣ n), a n)
      - ∑ n ∈ supp, a n * ∏ p ∈ d.primeFactors, g p
    let Rκ := ∑ T ∈ Pz.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D),
      kappaT Q g T * |r (∏ p ∈ T, p)|
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ K : ℝ, ∀ η : ℝ, 0 < η → ∀ Y : ℝ,
    ∃ (M : ℕ) (supp' : Finset ℕ) (a' : ℕ → ℝ) (P' : Set ℕ) (Q' : Finset ℕ) (g' : ℕ → ℕ → ℝ)
      (y₀ : ℝ),
      0 < M ∧
      (∀ n, 0 ≤ a' n) ∧ (∀ n, n ∉ supp' → a' n = 0) ∧ (∀ p ∈ P', p.Prime) ∧ (↑Q' ⊆ P') ∧
      (∀ n, ∀ p ∈ P', 0 ≤ g' n p ∧ g' n p < 1) ∧
      Y ≤ y₀ ∧ log (exp (M * ((1 + εF) * log z))) ≤ K * log y₀ ∧
      (∀ p ∈ P', p ∉ Q' → y₀ ≤ (p : ℝ)) ∧
      (∀ n, ∀ p ∈ P', p ∉ Q' → g' n p ≤ (1 + η) / (p : ℝ)) ∧
      ∑ n ∈ supp'.filter (fun n => ∀ p ∈ (range ⌈exp (M * ((1 + εF) * log z))⌉₊).filter
          (fun p => p ∈ P' ∧ (p : ℝ) < exp (M * ((1 + εF) * log z))), ¬ p ∣ n), a' n = S ∧
      ∑ n ∈ supp', a' n * ∏ p ∈ (range ⌈exp (M * ((1 + εF) * log z))⌉₊).filter
          (fun p => p ∈ P' ∧ (p : ℝ) < exp (M * ((1 + εF) * log z))), (1 - g' n p) = X ∧
      ∑ T ∈ ((range ⌈exp (M * ((1 + εF) * log z))⌉₊).filter
          (fun p => p ∈ P' ∧ (p : ℝ) < exp (M * ((1 + εF) * log z)))).powerset.filter
          (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q', p : ℕ) * (D * (1 - δ)) ^ M),
        |(∑ n ∈ supp'.filter (fun n => (∏ p ∈ T, p) ∣ n), a' n)
          - ∑ n ∈ supp', a' n * ∏ p ∈ (∏ p ∈ T, p).primeFactors, g' n p| ≤ Rκ := by
  sorry

/-- LEAF: step 7 of the hand proof of `fixedKappa_of_allLevels`: the new system is all primes of a
range at density near 1/p', so it satisfies `AllLevelsPremise` with ε. Levels u below y₀ reduce to
y₀, levels with w ≤ y₀ give the empty product. For y₀ ≤ u < w ≤ z' the ratio log w / log u is at most
K, so ∏ (1 - (1 + η)/p)⁻¹ ≤ (log w / log u)^{1+η} (1 + O(1/log² u)) ≤ (1 + ε) log w / log u once
K^η and the Mertens error are small. HARD: explicit Mertens, Rosser and Schoenfeld type, not in
Mathlib. Strictly easier than the parent: no construction and no sieve. Non-vacuity: P' = Q' = ∅
meets every hypothesis, and so does P' the primes of [y₀, z') with g' = 1/p. -/
theorem premise_of_range {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∃ Y : ℝ, ∀ (P' : Set ℕ) (Q' : Finset ℕ) (g' : ℕ → ℕ → ℝ) (z' y₀ : ℝ),
      (∀ p ∈ P', p.Prime) → (∀ n, ∀ p ∈ P', 0 ≤ g' n p ∧ g' n p < 1) →
      Y ≤ y₀ → log z' ≤ K * log y₀ →
      (∀ p ∈ P', p ∉ Q' → y₀ ≤ (p : ℝ)) →
      (∀ n, ∀ p ∈ P', p ∉ Q' → g' n p ≤ (1 + η) / (p : ℝ)) →
      AllLevelsPremise P' Q' g' ε z' := by
  sorry

/-- The level of the lifted system, PROVED: log D' / log z' = sδ for every M ≥ 1. -/
theorem lifted_level (z D εF δ : ℝ) (M : ℕ) (hM : 0 < M) (hlogz : 0 < log z) (h1 : 0 < 1 + εF) :
    log ((D * (1 - δ)) ^ M) / log (exp (M * ((1 + εF) * log z)))
      = log (D * (1 - δ)) / log z / (1 + εF) := by
  rw [Real.log_pow, Real.log_exp]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  field_simp

/-- The size conditions of the lifted system, PROVED: z^c < D(1 - δ) gives exp(M c log z) ≤ D'. -/
theorem lifted_size (z D δ c : ℝ) (M : ℕ) (hz : 0 < z) (h : z ^ c < D * (1 - δ)) :
    exp (M * (c * log z)) ≤ (D * (1 - δ)) ^ M := by
  have e : exp (M * (c * log z)) = (z ^ c) ^ M := by
    rw [rpow_def_of_pos hz, ← Real.exp_nat_mul]; ring_nf
  rw [e]
  exact pow_le_pow_left₀ (rpow_pos_of_pos hz _).le h.le M

/-- **Assembly**, CONDITIONAL ON `lift_exists` and `premise_of_range`: the leaf statement verbatim. -/
theorem lifted_bound_of_allLevels_split {εF ε C₁ C₂ : ℝ} (h : LinearSieveAllLevels ε C₁ C₂) :
  ∀ (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ),
    (∀ n, 0 ≤ a n) → (∀ n, n ∉ supp → a n = 0) → (∀ p ∈ P, p.Prime) → (↑Q ⊆ P) →
    (∀ q ∈ Q, (q : ℝ) < z) → (∀ p ∈ P, 0 < g p ∧ g p < 1) →
    0 < εF → 0 < ε → ε < 1 / 63 → 2 ≤ z →
    FixedPremise P Q g εF z →
    let Pz := (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ (p : ℝ) < z)
    let S := ∑ n ∈ supp.filter (fun n => ∀ p ∈ Pz, ¬ p ∣ n), a n
    let X := ∑ n ∈ supp, a n * ∏ p ∈ Pz, (1 - g p)
    let r := fun d : ℕ => (∑ n ∈ supp.filter (fun n => d ∣ n), a n)
      - ∑ n ∈ supp, a n * ∏ p ∈ d.primeFactors, g p
    let Rκ := ∑ T ∈ Pz.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D),
      kappaT Q g T * |r (∏ p ∈ T, p)|
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    let sδ := log (D * (1 - δ)) / log z / (1 + εF)
    (z ^ (1 + εF) < D * (1 - δ) → log D / log z / (1 + εF) ≤ 3 →
      S ≤ (2 * exp eulerMascheroniConstant / sδ + ε * C₁ * exp 2 * hS sδ) * X + Rκ) ∧
    (z ^ (2 * (1 + εF)) < D * (1 - δ) → log D / log z / (1 + εF) ≤ 4 →
      (2 * exp eulerMascheroniConstant * log (sδ - 1) / sδ - ε * C₂ * exp 2 * hS sδ) * X - Rκ
        ≤ S) := by
  intro supp a P Q g z D ha hs hP hQ hQz hg hεF hε hε63 hz hfix
  intro Pz S X r Rκ δ hδ0 hδ1 sδ
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < log z := log_pos (by linarith : 1 < z)
  have h1εF : 0 < 1 + εF := by linarith
  obtain ⟨K, hK⟩ := lift_exists (εF := εF) supp a P Q g z D ha hs hP hQ hQz hg hεF hz hfix
    δ hδ0 hδ1
  obtain ⟨η, hη, Y, hY⟩ := premise_of_range hε K
  obtain ⟨M, supp', a', P', Q', g', y₀, hM, ha', hs', hP', hQ', hg', hY0, hK0, hlarge, hgη,
    hSeq, hXeq, hReq⟩ := hK η hη Y
  have hprem := hY P' Q' g' _ y₀ hP' hg' hY0 hK0 hlarge hgη
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hz' : 2 ≤ exp (M * ((1 + εF) * log z)) := by
    have hl2 : log 2 ≤ log z := log_le_log (by norm_num) hz
    have : log 2 ≤ M * ((1 + εF) * log z) := by
      have : log z ≤ (1 + εF) * log z := by nlinarith
      have : (1 + εF) * log z ≤ M * ((1 + εF) * log z) := by nlinarith
      linarith
    calc (2 : ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
      _ ≤ _ := exp_le_exp.2 this
  have H := h supp' a' P' Q' g' _ ((D * (1 - δ)) ^ M) ha' hs' hP' hQ' hg' hε hε63 hz' hprem
  dsimp only at H
  rw [lifted_level z D εF δ M hM hlogz h1εF] at H
  simp only [hSeq, hXeq] at H
  have hsδle : ∀ c : ℝ, 0 < D * (1 - δ) → sδ ≤ log D / log z / (1 + εF) := by
    intro _ hDδ
    have hD0 : 0 < D := by
      by_contra hn; have hn2 := not_lt.1 hn; nlinarith
    have : log (D * (1 - δ)) ≤ log D := log_le_log hDδ (by nlinarith)
    show log (D * (1 - δ)) / log z / (1 + εF) ≤ log D / log z / (1 + εF)
    apply div_le_div_of_nonneg_right _ h1εF.le
    exact div_le_div_of_nonneg_right this hlogz.le
  refine ⟨fun hD hs3 => ?_, fun hD hs4 => ?_⟩
  · have hDδ : 0 < D * (1 - δ) := lt_trans (rpow_pos_of_pos hzpos _) hD
    have hsz : exp (M * ((1 + εF) * log z)) ≤ (D * (1 - δ)) ^ M :=
      lifted_size z D δ (1 + εF) M hzpos hD
    have := (H.1 hsz (le_trans (hsδle 0 hDδ) hs3))
    refine le_trans (le_of_eq ?_) (le_trans this ?_)
    · convert hSeq.symm
    · refine add_le_add le_rfl ?_
      convert hReq using 1
  · have hDδ : 0 < D * (1 - δ) := lt_trans (rpow_pos_of_pos hzpos _) hD
    have hsz : exp (M * ((1 + εF) * log z)) ^ 2 ≤ (D * (1 - δ)) ^ M := by
      have := lifted_size z D δ (2 * (1 + εF)) M hzpos hD
      rw [← Real.exp_nat_mul] at *
      convert this using 2; push_cast; ring
    have := (H.2 hsz (le_trans (hsδle 0 hDδ) hs4))
    refine le_trans ?_ (le_trans this (le_of_eq ?_))
    · refine sub_le_sub le_rfl ?_
      convert hReq using 1
    · convert hSeq

end LeanLab.BS2022GRH.SieveAllLevels1611

#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.lift_exists
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.premise_of_range
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.lifted_level
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.lifted_size
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.lifted_bound_of_allLevels_split
