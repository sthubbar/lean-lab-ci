/-
BS2022GRH, P0021, idea I-0088, F-0075, unit U-1611 closing REQUEST U-1606, run 20261103T0803Z-22341.
Second reader of the repair in research/novelty/FALSIFY-U1605-20261102.md Section 2.

Source: Bordignon, Starichkova, Ramanujan J. 64 (2024), Theorem 4 p. 1218, Lemma 7 p. 1221; Bordignon,
Johnston, Starichkova, IJNT 2025, Theorem 2.1, Lemma 2.7 with (2.26), (2.27), (2.32), Proposition 2.9.

The issue: `ChenThresholdGRH.LinearSieveT4` has condition (2) at the one sifting level z. The written
induction of Lemma 2.7 applies the case n - 1 at the level p < z, through
T_n(D,z) = sum_p g(p) T_{n-1}(D/p, p), so it uses (2) at every level. Hence:

* `LinearSieveAllLevels`, CITED, the content the written proof gives.
* `allLevels_of_T4`, PROVED: the printed fixed level statement implies it, so it is the weaker input.
* `LinearSieveFixedKappa`: the fixed level bound at s/(1+εF) with κ weights in the remainder.
* `fixedKappa_of_allLevels`, OPEN, a named sorry: the reduction, hand proof in its doc comment.
* `block_kappa_le`, `position_of_fixed`, `size_lift`, `kappaT_one_le`, PROVED: its finite algebra.
* `fixedPremise_of_lemma7`, CONDITIONAL ON Lemma 7: the premise of the reduction at the real system.
* `allLevelsPremise_instance`, `fixedPremise_instance`, `fixed_not_allLevels`, PROVED: vacuity
  instances, and the two premises differ.

This is NOT a claim of an error in the paper. `LinearSieveT4` is not shown false here.
AI wrote this Lean code, Claude, unit U-1611. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.ChenThresholdGRH

namespace LeanLab.BS2022GRH.SieveAllLevels1611
open Real Finset Classical
open LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH

/-! ### The all levels condition and the cited sieve -/

/-- Condition (2.27) at every pair of levels `1 < u < w ≤ z`, for the primes outside `Q`. -/
def AllLevelsPremise (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (ε z : ℝ) : Prop :=
  ∀ n u w, 1 < u → u < w → w ≤ z →
    ∏ p ∈ (range ⌈w⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w),
      (1 - g n p)⁻¹ ≤ (1 + ε) * (log w / log u)

/-- **Theorem 4 at all levels**, CITED from Bordignon, Johnston, Starichkova, Theorem 2.1 and Lemma 2.7,
journal P0021 p. 1218. The conclusion is word for word that of `LinearSieveT4`; the only change is
that (2) is asked at every pair of levels up to z, which is what the induction of Lemma 2.7 uses.
Other sources state it so: Maynard 1504.00533 eq. 7, Dudek and Dunn 2602.22720, as quoted by U-1605. -/
def LinearSieveAllLevels (ε C₁ C₂ : ℝ) : Prop :=
  ∀ (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D : ℝ),
    (∀ n, 0 ≤ a n) → (∀ n, n ∉ supp → a n = 0) → (∀ p ∈ P, p.Prime) → (↑Q ⊆ P) →
    (∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) → 0 < ε → ε < 1 / 63 → 2 ≤ z →
    AllLevelsPremise P Q g ε z →
    let Pz := (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ (p : ℝ) < z)
    let S := ∑ n ∈ supp.filter (fun n => ∀ p ∈ Pz, ¬ p ∣ n), a n
    let X := ∑ n ∈ supp, a n * ∏ p ∈ Pz, (1 - g n p)
    let r := fun d : ℕ => (∑ n ∈ supp.filter (fun n => d ∣ n), a n)
      - ∑ n ∈ supp, a n * ∏ p ∈ d.primeFactors, g n p
    let R := ∑ T ∈ Pz.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D),
      |r (∏ p ∈ T, p)|
    let s := log D / log z
    (z ≤ D → s ≤ 3 → S ≤ (2 * exp eulerMascheroniConstant / s + ε * C₁ * exp 2 * hS s) * X + R) ∧
    (z ^ 2 ≤ D → s ≤ 4 →
      (2 * exp eulerMascheroniConstant * log (s - 1) / s - ε * C₂ * exp 2 * hS s) * X - R ≤ S)

/-- **PROVED**: the printed fixed level sieve implies the all levels sieve. So `LinearSieveT4` is the
stronger input, the direction F-0075 reports. -/
theorem allLevels_of_T4 {ε C₁ C₂ : ℝ} (h : LinearSieveT4 ε C₁ C₂) :
    LinearSieveAllLevels ε C₁ C₂ := by
  intro supp a P Q g z D ha hs hP hQ hg h0 h1 hz hprem
  exact h supp a P Q g z D ha hs hP hQ hg h0 h1 hz (fun n u hu huz => hprem n u z hu huz le_rfl)

/-! ### The fixed level output of the reduction -/

/-- Display (2) at the one level `z`, with `g` independent of `n`. -/
def FixedPremise (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (εF z : ℝ) : Prop :=
  ∀ u, 1 < u → u < z →
    ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - g p)⁻¹ ≤ (1 + εF) * (log z / log u)

/-- κ(T) = ∏_{p ∈ T, p ∉ Q} (1 - g(p))⁻¹, the weight of the divisor ∏ T in the remainder. -/
noncomputable def kappaT (Q : Finset ℕ) (g : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∏ p ∈ T \ Q, (1 - g p)⁻¹

/-- **The fixed level sieve with κ**: condition (2) at the one level z, g independent of n and
positive, Q below z. Then the bounds of Theorem 4 hold at s* = s/(1+εF), for the row (ε, C₁, C₂) of
any ε, with the remainder R* = Σ κ(d)|r(d)| and z^{1+εF} < D, z^{2(1+εF)} < D.
The output of `fixedKappa_of_allLevels`. Not in the paper. -/
def LinearSieveFixedKappa (εF ε C₁ C₂ : ℝ) : Prop :=
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
    let sS := log D / log z / (1 + εF)
    (z ^ (1 + εF) < D → sS ≤ 3 →
      S ≤ (2 * exp eulerMascheroniConstant / sS + ε * C₁ * exp 2 * hS sS) * X + Rκ) ∧
    (z ^ (2 * (1 + εF)) < D → sS ≤ 4 →
      (2 * exp eulerMascheroniConstant * log (sS - 1) / sS - ε * C₂ * exp 2 * hS sS) * X - Rκ ≤ S)

/-- **The reduction**, OPEN, a named sorry, more than 30 minutes of Lean: it needs Mertens on all
primes of a range and the construction of the new integers. U-1611 read the hand proof line by line
and AGREES, with three repairs of U-1605: g > 0, strict D, Q below z. Hand proof:
Let p₁ > ... > p_k be the sifting primes outside Q, W_i = ∏_{j ≤ i} (1 - g(p_j))⁻¹, C = (1 + εF) log z.
1. Display (2) at u = p_i gives log p_i ≤ C/W_i, `position_of_fixed`.
2. For large M let B_i be the primes, not used in step 3, with log p' in M[C/W_i, C/W_{i-1}); nonempty as
   g(p_i) > 0. Put g'(p') = c_i/p' with c_i chosen so that ∏_{B_i}(1 - g') = 1 - g(p_i); Mertens gives
   c_i → 1. Numbers: reduction_check.py Part B.
3. Each q ∈ Q goes to a new prime q' ≥ q^M with q' ≤ q^M(1 + o(1)), g'(q') = g(q), q' < z' = exp(MC).
4. Send each n to n', the product of q' for q | n and of a subset T_i of B_i for p_i | n, T_i drawn from
   independent Bernoulli g' conditioned nonempty. Let a' be the image mass.
5. Then S' = S, X' = X, and r'(d') = c(T) r(d) for d' with image d, c(T) = ∏_i ∏_{p' ∈ T_i} g'(p')/g(p_i),
   and Σ_T c(T) ≤ κ(d) for every M, `block_kappa_le`. Exact check: reduction_check.py Part A.
6. Each prime of T_i is ≥ p_i^M, so d' ≥ d^M, `size_lift`. With D' = (D(1 - δ))^M, d' < Q'D' forces d < QD.
7. The new system satisfies `AllLevelsPremise` with ε for M large, since it is all primes of a range at
   density near 1/p'. Levels below the least new prime reduce to it, as the product is then empty.
8. `LinearSieveAllLevels` at z', D' gives the bound at s_M = log D'/log z' → s/(1+εF), and F, f, h are
   continuous there, so M → ∞, δ → 0 finishes. Strict D gives D' ≥ z', z'². -/
theorem fixedKappa_of_allLevels {εF ε C₁ C₂ : ℝ} (h : LinearSieveAllLevels ε C₁ C₂) :
    LinearSieveFixedKappa εF ε C₁ C₂ := by
  sorry

/-! ### The finite algebra of the reduction, PROVED -/

/-- κ ≥ 1, so R* is at least the printed R. -/
theorem kappaT_one_le (Q : Finset ℕ) (g : ℕ → ℝ) (T : Finset ℕ)
    (hg : ∀ p ∈ T \ Q, 0 ≤ g p ∧ g p < 1) : 1 ≤ kappaT Q g T := by
  unfold kappaT
  apply Finset.one_le_prod₀
  intro p hp
  obtain ⟨h0, h1⟩ := hg p hp
  have hpos : 0 < 1 - g p := by linarith
  rw [one_le_inv₀ hpos]
  linarith

/-- Step 5, one block: if ∏_B (1 - f) = 1 - γ, the sum of the weights c(T) over nonempty T ⊆ B is
(∏_B (1 + f) - 1)/γ, and it is at most (1 - γ)⁻¹. This holds at every M, not only in the limit. -/
theorem block_kappa_le (B : Finset ℕ) (f : ℕ → ℝ) (γ : ℝ)
    (hf : ∀ p ∈ B, 0 ≤ f p ∧ f p ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hprod : ∏ p ∈ B, (1 - f p) = 1 - γ) :
    (∏ p ∈ B, (1 + f p) - 1) / γ ≤ (1 - γ)⁻¹ := by
  have hmul : (∏ p ∈ B, (1 + f p)) * (1 - γ) ≤ 1 := by
    rw [← hprod, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_one₀
    · intro p hp
      obtain ⟨h0, h1⟩ := hf p hp
      exact mul_nonneg (by linarith) (by linarith)
    · intro p hp
      obtain ⟨h0, h1⟩ := hf p hp
      nlinarith
  have h1g : 0 < 1 - γ := by linarith
  have hne : 1 - γ ≠ 0 := h1g.ne'
  have hI : (1 - γ)⁻¹ * (1 - γ) = 1 := inv_mul_cancel₀ hne
  have h2 : ∏ p ∈ B, (1 + f p) ≤ (1 - γ)⁻¹ := by
    rw [← one_div, le_div_iff₀ h1g]; exact hmul
  have h3 : (1 - γ)⁻¹ * γ = (1 - γ)⁻¹ - 1 := by linear_combination -hI
  rw [div_le_iff₀ hγ0, h3]
  linarith

/-- Step 5, the same sum written over nonempty subsets. -/
theorem block_sum_eq (B : Finset ℕ) (f : ℕ → ℝ) :
    ∑ T ∈ B.powerset.filter (fun T => T.Nonempty), ∏ p ∈ T, f p = ∏ p ∈ B, (1 + f p) - 1 := by
  rw [Finset.prod_one_add, Finset.sum_filter]
  have h : (∑ T ∈ B.powerset, ∏ p ∈ T, f p)
      = ∑ T ∈ B.powerset, ((if T.Nonempty then ∏ p ∈ T, f p else 0)
          + if T = ∅ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T = ∅
    · subst hT; simp
    · have : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hT
      simp [hT, this]
  rw [h, Finset.sum_add_distrib]
  simp

/-- Step 1: display (2) at u = p puts the prime at or below its linear position,
log p ≤ (1 + εF) log z / W, W the product from p up. -/
theorem position_of_fixed {P : Set ℕ} {Q : Finset ℕ} {g : ℕ → ℝ} {εF z : ℝ}
    (h : FixedPremise P Q g εF z) {p : ℕ} (hp1 : 1 < p) (hpz : (p : ℝ) < z) :
    (∏ r ∈ (range ⌈z⌉₊).filter (fun r => r ∈ P ∧ r ∉ Q ∧ (p : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < z),
      (1 - g r)⁻¹) * log p ≤ (1 + εF) * log z := by
  have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1
  have hl : 0 < log (p : ℝ) := log_pos hp1'
  have := h p hp1' hpz
  rw [← mul_div_assoc, le_div_iff₀ hl] at this
  exact this

/-- Step 6: if each prime is lifted to at least its M-th power, d^M ≤ d'. -/
theorem size_lift (T : Finset ℕ) (φ : ℕ → ℕ) (M : ℕ) (h : ∀ p ∈ T, p ^ M ≤ φ p) :
    (∏ p ∈ T, p) ^ M ≤ ∏ p ∈ T, φ p := by
  rw [← Finset.prod_pow]
  exact Finset.prod_le_prod h

/-! ### The premise at the real system, CONDITIONAL ON Lemma 7 -/

/-- **Vacuity at the real system, CONDITIONAL ON `Lemma7J`**: with g(p) = 1/(p-1), P any set of primes,
Q holding the primes of P below u₀, u₀ ≥ 400 and z > exp 2753, `FixedPremise` holds with εF ≥ ε(u₀).
This is what the paper proves on p. 1229, and it is all the reduction asks. -/
theorem fixedPremise_of_lemma7 (hL : Lemma7J) {P : Set ℕ} {Q : Finset ℕ} {u₀ εF z : ℝ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, (p : ℝ) < u₀ → p ∈ Q)
    (hu : 400 ≤ u₀) (hu₀z : u₀ < z) (hz : exp 2753 < z) (hε : epsJ u₀ ≤ εF) :
    FixedPremise P Q (fun p => 1 / ((p : ℝ) - 1)) εF z := by
  intro v hv hvz
  set v' := max v u₀ with hv'
  have hv'z : v' < z := max_lt hvz hu₀z
  have hv'1 : 1 < v' := lt_of_lt_of_le hv (le_max_left _ _)
  obtain ⟨hlem, -⟩ := hL z u₀ v' hz hu (le_max_right _ _) hv'z
  have hsub : (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z) ⊆
      (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ v' ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hr, hpP, hpQ, hvp, hpz⟩ := hp
    refine ⟨hr, hP p hpP, ?_, hpz⟩
    have : u₀ ≤ (p : ℝ) := not_lt.1 (fun hlt => hpQ (hQ p hpP hlt))
    exact max_le hvp this
  have hone : ∀ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ v' ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 : ℝ) ≤ (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    intro p hp
    have hp2 := (Finset.mem_filter.1 hp).2.2.1
    have h400 : (400 : ℝ) ≤ p := hu.trans ((le_max_right _ _).trans hp2)
    have h0 : (0 : ℝ) < 1 / ((p : ℝ) - 1) := by
      apply one_div_pos.2; linarith
    have h1 : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hpos : 0 < 1 - 1 / ((p : ℝ) - 1) := by linarith
    rw [one_le_inv₀ hpos]
    linarith
  set A := (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z) with hA
  set B := (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ v' ≤ (p : ℝ) ∧ (p : ℝ) < z) with hB
  have hsplit : (∏ p ∈ B \ A, (1 - 1 / ((p : ℝ) - 1))⁻¹) * ∏ p ∈ A, (1 - 1 / ((p : ℝ) - 1))⁻¹
      = ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ := Finset.prod_sdiff hsub
  have hBA : 1 ≤ ∏ p ∈ B \ A, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
    Finset.one_le_prod₀ (fun p hp => hone p (Finset.mem_sdiff.1 hp).1)
  have hA1 : 0 ≤ ∏ p ∈ A, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
    Finset.prod_nonneg (fun p hp => le_trans zero_le_one (hone p (hsub hp)))
  have hB0 : 0 ≤ ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
    Finset.prod_nonneg (fun p hp => le_trans zero_le_one (hone p hp))
  have hAB : ∏ p ∈ A, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    rw [← hsplit]; nlinarith
  have hz1 : 1 < z := lt_trans hv hvz
  have hlz : 0 < log z := log_pos hz1
  have hlv : 0 < log v := log_pos hv
  have hlvv : log v ≤ log v' := log_le_log (by linarith) (le_max_left _ _)
  have hr : log z / log v' ≤ log z / log v :=
    div_le_div_of_nonneg_left hlz.le hlv hlvv
  have hR0 : 0 ≤ log z / log v' := div_nonneg hlz.le (by linarith)
  have hε1 : 0 ≤ 1 + epsJ u₀ := by
    by_contra hneg
    have hneg' := not_le.1 hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg'.le hR0
    linarith
  calc ∏ p ∈ A, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ := hAB
    _ ≤ (1 + epsJ u₀) * (log z / log v') := hlem.le
    _ ≤ (1 + εF) * (log z / log v') :=
        mul_le_mul_of_nonneg_right (by linarith) hR0
    _ ≤ (1 + εF) * (log z / log v) :=
        mul_le_mul_of_nonneg_left hr (by linarith)

/-! ### Vacuity instances, PROVED -/

/-- A product over a set of at most the prime 5. -/
lemma five_prod_le {S : Finset ℕ} {f : ℕ → ℝ} {c : ℝ} (hS : ∀ p ∈ S, p = 5) (h1 : 1 ≤ c)
    (h5 : 5 ∈ S → f 5 ≤ c) : ∏ p ∈ S, f p ≤ c := by
  by_cases hm : 5 ∈ S
  · have : S = {5} := by
      ext p; simp only [Finset.mem_singleton]
      exact ⟨hS p, fun h => h ▸ hm⟩
    rw [this, Finset.prod_singleton]
    exact h5 hm
  · have : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      exact hm (hS p hp ▸ hp)
    rw [this, Finset.prod_empty]
    exact h1

lemma five_of_prod_le {S : Finset ℕ} {f : ℕ → ℝ} {c : ℝ} (hS : ∀ p ∈ S, p = 5) (h5 : 5 ∈ S)
    (h : ∏ p ∈ S, f p ≤ c) : f 5 ≤ c := by
  have : S = {5} := by
    ext p; simp only [Finset.mem_singleton]
    exact ⟨hS p, fun h => h ▸ h5⟩
  rw [this, Finset.prod_singleton] at h
  exact h

lemma one_le_log_ratio {u w : ℝ} (hu : 1 < u) (huw : u < w) : 1 ≤ log w / log u := by
  have hl : 0 < log u := log_pos hu
  rw [one_le_div hl]
  exact log_le_log (by linarith) huw.le

/-- **Vacuity of `LinearSieveAllLevels`'s premise**, a real prime with positive density at every level:
P = {5}, g = ε/(1+ε), so the single factor is exactly 1 + ε. -/
theorem allLevelsPremise_instance {ε z : ℝ} (hε : 0 < ε) :
    AllLevelsPremise {5} ∅ (fun _ _ => ε / (1 + ε)) ε z := by
  intro n u w hu huw _
  have hr := one_le_log_ratio hu huw
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have hne : 1 + ε ≠ 0 := h1.ne'
  have h2 : (1 - ε / (1 + ε)) * (1 + ε) = 1 := by
    rw [sub_mul, div_mul_cancel₀ _ hne]; ring
  have hfac : (1 - ε / (1 + ε))⁻¹ = 1 + ε := by
    rw [eq_inv_of_mul_eq_one_left h2, inv_inv]
  have hc : 1 + ε ≤ (1 + ε) * (log w / log u) := by nlinarith
  refine five_prod_le ?_ (by linarith) ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2.1
  · intro _
    show (1 - ε / (1 + ε))⁻¹ ≤ _
    rw [hfac]; exact hc

/-- **Vacuity of `LinearSieveFixedKappa`'s premise**: one heavy prime, g(5) = 1/2, at z = 1000. -/
theorem fixedPremise_instance : FixedPremise {5} ∅ (fun _ => 1 / 2) (1 / 100) 1000 := by
  intro u hu huz
  have hr := one_le_log_ratio hu huz
  refine five_prod_le ?_ (by nlinarith) ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2.1
  · intro hm
    simp only [Finset.mem_filter] at hm
    have hu5 : u ≤ 5 := by simpa using hm.2.2.2.1
    have hlu : 0 < log u := log_pos hu
    have hlu5 : log u ≤ log 5 := log_le_log (by linarith) hu5
    have h25 : 2 * log (5 : ℝ) ≤ log 1000 := by
      have h : log (25 : ℝ) ≤ log 1000 := log_le_log (by norm_num) (by norm_num)
      have e : log (25 : ℝ) = 2 * log 5 := by
        rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have hratio : 2 ≤ log 1000 / log u := by
      rw [le_div_iff₀ hlu]; linarith
    have e : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    show (1 - (1 / 2 : ℝ))⁻¹ ≤ _
    rw [e]
    nlinarith

/-- **The two premises differ**: the system of `fixedPremise_instance` fails all levels at u = 5,
w = 6, as a heavy prime must. So the reduction has real content. -/
theorem fixed_not_allLevels : ¬ AllLevelsPremise {5} ∅ (fun _ _ => 1 / 2) (1 / 100) 1000 := by
  intro h
  have h1 := h 0 5 6 (by norm_num) (by norm_num) (by norm_num)
  have h2 := five_of_prod_le
    (by
      intro p hp
      simp only [Finset.mem_filter] at hp
      simpa using hp.2.1)
    (by
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_range.2 (Nat.lt_ceil.2 (by norm_num)),
        by simp, by simp, by norm_num, by norm_num⟩) h1
  have h3 : (2 : ℝ) ≤ (1 + 1 / 100) * (log 6 / log 5) :=
    calc (2 : ℝ) = (1 - (1 / 2 : ℝ))⁻¹ := by norm_num
      _ ≤ _ := h2
  have hl5 : 0 < log (5 : ℝ) := log_pos (by norm_num)
  have hlog : 3 * log (6 : ℝ) ≤ 4 * log 5 := by
    have e1 : 3 * log (6 : ℝ) = log (216 : ℝ) := by
      rw [show (216 : ℝ) = 6 ^ 3 by norm_num, Real.log_pow]; norm_num
    have e2 : 4 * log (5 : ℝ) = log (625 : ℝ) := by
      rw [show (625 : ℝ) = 5 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [e1, e2]
    exact log_le_log (by norm_num) (by norm_num)
  have hr : log (6 : ℝ) / log 5 ≤ 4 / 3 := by
    rw [div_le_iff₀ hl5]; linarith
  linarith

end LeanLab.BS2022GRH.SieveAllLevels1611

#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.allLevels_of_T4
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.fixedKappa_of_allLevels
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.kappaT_one_le
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.block_kappa_le
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.block_sum_eq
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.position_of_fixed
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.size_lift
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.fixedPremise_of_lemma7
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.allLevelsPremise_instance
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.fixedPremise_instance
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.fixed_not_allLevels
