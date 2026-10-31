/-
P0016 Pintz 2018, arXiv 1804.09084v2, unit U-6775, CLOUD 20261021T0017Z-cloud54, T2.
Section 9 with slack in the weight: every case closes at `A' = 25/7 - 1/20000`, so
`ϑ' = 1/A' > 0.28` strictly, which answers the numerical half of QUESTION Q-1278a.

Read from papers/P0016.pdf pp. 38 to 43, pages rendered and checked by eye: (9.2), (9.4), (9.5),
(9.6), (9.20), (9.22) to (9.37). The weight of Section 9 is `e^{-Aλ}`, `A = 25/7`, everywhere.

Model of (9.2). A class `i ∈ I` has zeros `j ∈ Z i` with `λ_j ≤ H`, counted with multiplicity
through the index. `N_i(λ) = #{j : λ_j ≤ λ}` and `S_i = A ∫_0^H N_i(λ) e^{-Aλ} dλ` give, zero by
zero, `S_i = Σ_j (e^{-Aλ_j} - e^{-AH})`, split at `Λ` into
`a_i = Σ_j (e^{-A min(λ_j,Λ)} - e^{-AΛ})` and `b_i = Σ_j (e^{-A max(λ_j,Λ)} - e^{-AH})`;
`S_split` checks this.

Which printed numbers depend on `A`, and how they are handled:
* the `a`-sums of Lemma 7, (9.18), (9.20): transferred rigorously, `aS_scale`,
  `Σ a_i(A') ≤ e^{ηΛ} Σ a_i(A)`; in Cases 7 and 8 the single `a_1` is recomputed at `A'`.
* the constants `22.281`, `15.6`, `10.4` of (9.6), (9.27), (9.32) bound sums of
  `e^{-(8/3)λ}` and `e^{-2λ}`; they do not depend on `A`. The factors `e^{-19Λ/21}`,
  `e^{-(25/7 - 8/3)Λ*}`, `e^{-(25/7 - 2)Λ*}` do, and are recomputed at `A'`.
* Lemma 6, `max b_i ≤ c*_j`, (9.5) and (9.28), comes from Theorem I numerics at `A = 25/7` that
  are not reproduced. It is kept as a hypothesis AT `A = 25/7`, quoted, and moved to `A'` by the
  convexity transfer `bS_transfer`, `b_i(A') ≤ α b_i(A) + β b_i(8/3)` with
  `α = (A'/A) t e^c`, `β = (A'/B)(1-t) e^d`, `A' = tA + (1-t)B`, `tc + (1-t)d = 0`.

The results are CONDITIONAL ON the quoted inputs named in each statement: Lemma 6 and Lemma 7
values at `A = 25/7`, the Corollary 1 totals, and the zero-location facts from Tables 4, 5, 7 of
the paper's reference [9] and Theorem G. Theorems A to L are not proved. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Pintz2018.Numbers
import LeanLab.ExceptionalSet.Pintz2018Reduction

namespace LeanLab.ExceptionalSet.Pintz2018Slack
open Real Finset

/-! ### The zero-sum model of (9.2) -/

section Model
variable {ι κ : Type*}

/-- `a_i` of (9.2) at weight `A` and cut `Λ`: `Σ_j (e^{-A min(λ_j,Λ)} - e^{-AΛ})`. -/
noncomputable def aS (A Λ : ℝ) (s : Finset ι) (lam : ι → ℝ) : ℝ :=
  ∑ j ∈ s, (exp (-(A * min (lam j) Λ)) - exp (-(A * Λ)))

/-- `b_i` of (9.2) and p. 43: `A ∫_Λ^H N_i(λ) e^{-Aλ} dλ = Σ_j (e^{-A max(λ_j,Λ)} - e^{-AH})`. -/
noncomputable def bS (A Λ H : ℝ) (s : Finset ι) (lam : ι → ℝ) : ℝ :=
  ∑ j ∈ s, (exp (-(A * max (lam j) Λ)) - exp (-(A * H)))

/-- The Corollary 1 sum `Σ_j e^{-B max(λ_j,Λ)}` of (9.6), with `B = 8/3` there. -/
noncomputable def KS (B Λ : ℝ) (s : Finset ι) (lam : ι → ℝ) : ℝ :=
  ∑ j ∈ s, exp (-(B * max (lam j) Λ))

/-- Faithfulness of the split: `a_i + b_i = Σ_j (e^{-Aλ_j} - e^{-AH}) = S_i`, for every `Λ`. -/
theorem S_split (A Λ H : ℝ) (s : Finset ι) (lam : ι → ℝ) :
    aS A Λ s lam + bS A Λ H s lam = ∑ j ∈ s, (exp (-(A * lam j)) - exp (-(A * H))) := by
  unfold aS bS
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rcases le_total (lam j) Λ with h | h
  · rw [min_eq_left h, max_eq_right h]; ring
  · rw [min_eq_right h, max_eq_left h]; ring

theorem aS_nonneg {A Λ : ℝ} (hA : 0 ≤ A) (s : Finset ι) (lam : ι → ℝ) : 0 ≤ aS A Λ s lam := by
  apply sum_nonneg
  intro j _
  have : exp (-(A * Λ)) ≤ exp (-(A * min (lam j) Λ)) :=
    exp_le_exp.mpr (by nlinarith [min_le_right (lam j) Λ])
  linarith

theorem bS_nonneg {A Λ H : ℝ} (hA : 0 ≤ A) {s : Finset ι} {lam : ι → ℝ}
    (hs : ∀ j ∈ s, lam j ≤ H) (hΛ : Λ ≤ H) : 0 ≤ bS A Λ H s lam := by
  apply sum_nonneg
  intro j hj
  have : exp (-(A * H)) ≤ exp (-(A * max (lam j) Λ)) :=
    exp_le_exp.mpr (by nlinarith [max_le (hs j hj) hΛ])
  linarith

theorem bS_le_KS (B Λ H : ℝ) (s : Finset ι) (lam : ι → ℝ) : bS B Λ H s lam ≤ KS B Λ s lam := by
  unfold bS KS
  apply sum_le_sum
  intro j _
  linarith [exp_pos (-(B * H))]

theorem KS_nonneg (B Λ : ℝ) (s : Finset ι) (lam : ι → ℝ) : 0 ≤ KS B Λ s lam :=
  sum_nonneg fun _ _ => (exp_pos _).le

/-- The step of (9.6) and (9.27): `Σ_j e^{-A max(λ_j,Λ)} ≤ e^{-(A-B)Λ} Σ_j e^{-B max(λ_j,Λ)}`
for `A ≥ B`, so `b_i ≤ e^{-(A-B)Λ} K_i`. -/
theorem bS_tail {A B Λ H : ℝ} (hAB : B ≤ A) (s : Finset ι) (lam : ι → ℝ) :
    bS A Λ H s lam ≤ exp (-((A - B) * Λ)) * KS B Λ s lam := by
  unfold bS KS
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  have h1 : exp (-(A * max (lam j) Λ)) = exp (-((A - B) * max (lam j) Λ)) *
      exp (-(B * max (lam j) Λ)) := by rw [← exp_add]; ring_nf
  have h2 : exp (-((A - B) * max (lam j) Λ)) ≤ exp (-((A - B) * Λ)) :=
    exp_le_exp.mpr (by nlinarith [le_max_right (lam j) Λ])
  have h3 := exp_pos (-(B * max (lam j) Λ))
  have h4 := exp_pos (-(A * H))
  nlinarith

/-- Transfer of the `a`-sums: for `η ≥ 0`, `a_i(A - η) ≤ e^{ηΛ} a_i(A)`, any configuration. -/
theorem aS_scale {A η Λ : ℝ} (hη : 0 ≤ η) (s : Finset ι) (lam : ι → ℝ) :
    aS (A - η) Λ s lam ≤ exp (η * Λ) * aS A Λ s lam := by
  unfold aS
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  set μ := min (lam j) Λ
  have h1 : exp (-((A - η) * μ)) = exp (η * μ) * exp (-(A * μ)) := by rw [← exp_add]; ring_nf
  have h2 : exp (-((A - η) * Λ)) = exp (η * Λ) * exp (-(A * Λ)) := by rw [← exp_add]; ring_nf
  have h3 : exp (η * μ) ≤ exp (η * Λ) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right _ _) hη)
  have h4 := exp_pos (-(A * μ))
  rw [h1, h2]
  nlinarith

/-! ### The convexity transfer for `b_i` -/

/-- Pointwise: with `A' = tA + (1-t)B` and `tc + (1-t)d = 0`,
`e^{-A'x} ≤ t e^c e^{-Ax} + (1-t) e^d e^{-Bx}` for every real `x`. -/
theorem exp_interp {A B A' t c d : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hA' : A' = t * A + (1 - t) * B) (hcd : t * c + (1 - t) * d = 0) (x : ℝ) :
    exp (-(A' * x)) ≤ t * exp c * exp (-(A * x)) + (1 - t) * exp d * exp (-(B * x)) := by
  have h := convexOn_exp.2 (Set.mem_univ (c + -(A * x))) (Set.mem_univ (d + -(B * x)))
    ht0 (sub_nonneg.mpr ht1) (by ring)
  simp only [smul_eq_mul] at h
  have e1 : t * (c + -(A * x)) + (1 - t) * (d + -(B * x)) = -(A' * x) := by
    rw [hA']; linear_combination hcd
  rw [e1, exp_add, exp_add] at h
  calc exp (-(A' * x)) ≤ t * (exp c * exp (-(A * x))) + (1 - t) * (exp d * exp (-(B * x))) := h
    _ = _ := by ring

/-- Integrated over `[m, H]`: `e^{-A'm} - e^{-A'H} ≤ α (e^{-Am} - e^{-AH}) + β (e^{-Bm} - e^{-BH})`
with `α = (A'/A) t e^c`, `β = (A'/B)(1-t) e^d`, for `m ≤ H`. -/
theorem tail_interp {A B A' t c d : ℝ} (hA : 0 < A) (hB : 0 < B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hA' : A' = t * A + (1 - t) * B) (hcd : t * c + (1 - t) * d = 0) {m H : ℝ} (hmH : m ≤ H) :
    exp (-(A' * m)) - exp (-(A' * H)) ≤
      A' / A * t * exp c * (exp (-(A * m)) - exp (-(A * H))) +
      A' / B * (1 - t) * exp d * (exp (-(B * m)) - exp (-(B * H))) := by
  set α := A' / A * t * exp c
  set β := A' / B * (1 - t) * exp d
  have hA'0 : 0 ≤ A' := by rw [hA']; nlinarith
  let φ : ℝ → ℝ := fun x => α * exp (-(A * x)) + β * exp (-(B * x)) - exp (-(A' * x))
  have hd : ∀ x, HasDerivAt φ (α * (exp (-(A * x)) * -(A * 1)) + β * (exp (-(B * x)) * -(B * 1))
      - exp (-(A' * x)) * -(A' * 1)) x := by
    intro x
    have h1 := (((hasDerivAt_id x).const_mul A).neg.exp).const_mul α
    have h2 := (((hasDerivAt_id x).const_mul B).neg.exp).const_mul β
    have h3 := ((hasDerivAt_id x).const_mul A').neg.exp
    exact (h1.add h2).sub h3
  have hanti : Antitone φ := by
    apply antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    have hp := exp_interp ht0 ht1 hA' hcd x
    have e1 : α * A = A' * t * exp c := by simp only [α]; field_simp
    have e2 : β * B = A' * (1 - t) * exp d := by simp only [β]; field_simp
    have hm := mul_le_mul_of_nonneg_left hp hA'0
    have k1 : α * (exp (-(A * x)) * -(A * 1)) = -(A' * t * exp c * exp (-(A * x))) := by
      rw [← e1]; ring
    have k2 : β * (exp (-(B * x)) * -(B * 1)) = -(A' * (1 - t) * exp d * exp (-(B * x))) := by
      rw [← e2]; ring
    rw [k1, k2]
    nlinarith
  have := hanti hmH
  simp only [φ] at this
  linarith

/-- Lemma 6 transferred: `b_i(A') ≤ α b_i(A) + β b_i(B)`. -/
theorem bS_transfer {A B A' t c d Λ H : ℝ} (hA : 0 < A) (hB : 0 < B) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hA' : A' = t * A + (1 - t) * B) (hcd : t * c + (1 - t) * d = 0)
    {s : Finset ι} {lam : ι → ℝ} (hs : ∀ j ∈ s, lam j ≤ H) (hΛ : Λ ≤ H) :
    bS A' Λ H s lam ≤
      A' / A * t * exp c * bS A Λ H s lam + A' / B * (1 - t) * exp d * bS B Λ H s lam := by
  unfold bS
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro j hj
  exact tail_interp hA hB ht0 ht1 hA' hcd (max_le (hs j hj) hΛ)

/-- With a single zero below `Λ`, the total `a`-sum is that zero's term. -/
theorem aS_single {A Λ : ℝ} {I : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {i1 : κ} {j1 : ι}
    (hi1 : i1 ∈ I) (hj1 : j1 ∈ Z i1)
    (hsingle : ∀ i ∈ I, ∀ j ∈ Z i, lam j < Λ → i = i1 ∧ j = j1) :
    ∑ i ∈ I, aS A Λ (Z i) lam = exp (-(A * min (lam j1) Λ)) - exp (-(A * Λ)) := by
  have hz : ∀ i ∈ I, ∀ j ∈ Z i, ¬ (i = i1 ∧ j = j1) →
      exp (-(A * min (lam j) Λ)) - exp (-(A * Λ)) = 0 := by
    intro i hi j hj hne
    have : Λ ≤ lam j := by
      by_contra h; push Not at h; exact hne (hsingle i hi j hj h)
    rw [min_eq_right this]; ring
  rw [sum_eq_single_of_mem i1 hi1]
  · unfold aS
    rw [sum_eq_single_of_mem j1 hj1]
    intro j hj hne
    exact hz i1 hi1 j hj (fun h => hne h.2)
  · intro i hi hne
    unfold aS
    exact sum_eq_zero fun j hj => hz i hi j hj (fun h => hne h.1)

/-- The refined form of (9.4) used in (9.22) to (9.26): all classes have `b_i ≤ c₁` except
those in `I₂`, at most two, with `b_i ≤ c₂`, and those in `I₃`, at most two, with `b_i ≤ c₃`. -/
theorem refined_ineq (I I2 I3 : Finset κ) (a b : κ → ℝ) {Aa Bb c1 c2 c3 : ℝ}
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i) (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2)
    (hc23 : c2 ≤ c3) (h1 : ∀ i ∈ I, i ∉ I2 → i ∉ I3 → b i ≤ c1) (h2 : ∀ i ∈ I, i ∈ I2 → b i ≤ c2)
    (h3 : ∀ i ∈ I, b i ≤ c3) (hI2 : I2.card ≤ 2) (hI3 : I3.card ≤ 2)
    (hA : ∑ i ∈ I, a i ≤ Aa) (hB : ∑ i ∈ I, b i ≤ Bb) :
    ∑ i ∈ I, (a i + b i) ^ 2 ≤
      Aa ^ 2 + c1 * (2 * Aa + Bb) + (c3 - c1) * (2 * Aa + 2 * c3) + (c2 - c1) * (2 * c2) := by
  classical
  -- the `a`-square part, from `basic_ineq` with `b = 0`
  have hsq : ∑ i ∈ I, a i ^ 2 ≤ Aa ^ 2 := by
    have := LeanLab.Pintz2018.basic_ineq I a (fun _ => 0) 0 Aa 0 le_rfl ha (fun _ _ => le_rfl)
      (fun _ _ => le_rfl) hA (by simp)
    simpa using this
  have hA0 : 0 ≤ ∑ i ∈ I, a i := sum_nonneg ha
  have hab : ∑ i ∈ I, a i * b i ≤ c3 * Aa := by
    calc ∑ i ∈ I, a i * b i ≤ ∑ i ∈ I, a i * c3 :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h3 i hi) (ha i hi)
      _ = c3 * ∑ i ∈ I, a i := by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ ≤ c3 * Aa := mul_le_mul_of_nonneg_left hA (by linarith)
  -- the `b`-square part
  let m : κ → ℝ := fun i => c1 + (if i ∈ I3 then c3 - c1 else 0) + (if i ∈ I2 then c2 - c1 else 0)
  have hbm : ∀ i ∈ I, b i ≤ m i := by
    intro i hi
    simp only [m]
    by_cases h3' : i ∈ I3 <;> by_cases h2' : i ∈ I2 <;> simp only [h3', h2', ite_true, ite_false]
    · linarith [h3 i hi]
    · linarith [h3 i hi]
    · linarith [h2 i hi h2']
    · linarith [h1 i hi h2' h3']
  have hbb : ∑ i ∈ I, b i ^ 2 ≤ ∑ i ∈ I, b i * m i :=
    sum_le_sum fun i hi => by rw [sq]; exact mul_le_mul_of_nonneg_left (hbm i hi) (hb i hi)
  have hsplit : ∑ i ∈ I, b i * m i = c1 * ∑ i ∈ I, b i
      + (c3 - c1) * ∑ i ∈ I.filter (· ∈ I3), b i + (c2 - c1) * ∑ i ∈ I.filter (· ∈ I2), b i := by
    rw [sum_filter, sum_filter, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    simp only [m]
    split_ifs <;> ring
  have hcard : ∀ (J : Finset κ) (c : ℝ), J.card ≤ 2 → 0 ≤ c → (∀ i ∈ I, i ∈ J → b i ≤ c) →
      ∑ i ∈ I.filter (· ∈ J), b i ≤ 2 * c := by
    intro J c hJ hc hbJ
    have hsub : (I.filter (· ∈ J)).card ≤ 2 :=
      (card_le_card (fun x hx => (mem_filter.mp hx).2)).trans hJ
    calc ∑ i ∈ I.filter (· ∈ J), b i ≤ (I.filter (· ∈ J)).card • c :=
          sum_le_card_nsmul _ _ _ fun i hi => hbJ i (mem_filter.mp hi).1 (mem_filter.mp hi).2
      _ = ((I.filter (· ∈ J)).card : ℝ) * c := nsmul_eq_mul _ _
      _ ≤ 2 * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) hc
  have hs3 := hcard I3 c3 hI3 (by linarith) (fun i hi _ => h3 i hi)
  have hs2 := hcard I2 c2 hI2 (by linarith) (fun i hi h => h2 i hi h)
  have hexp : ∑ i ∈ I, (a i + b i) ^ 2 =
      ∑ i ∈ I, a i ^ 2 + 2 * ∑ i ∈ I, a i * b i + ∑ i ∈ I, b i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hB1 : c1 * ∑ i ∈ I, b i ≤ c1 * Bb := mul_le_mul_of_nonneg_left hB hc1
  have hd3 : (c3 - c1) * ∑ i ∈ I.filter (· ∈ I3), b i ≤ (c3 - c1) * (2 * c3) :=
    mul_le_mul_of_nonneg_left hs3 (by linarith)
  have hd2 : (c2 - c1) * ∑ i ∈ I.filter (· ∈ I2), b i ≤ (c2 - c1) * (2 * c2) :=
    mul_le_mul_of_nonneg_left hs2 (by linarith)
  rw [hexp]
  nlinarith

end Model

/-! ### Parameters -/

/-- The reduced weight `A' = 25/7 - η`, `η = 1/20000`. -/
noncomputable def Ap : ℝ := 25 / 7 - 1 / 20000

theorem Ap_eq : Ap = 499993 / 140000 := by unfold Ap; norm_num

/-- `ϑ' = 1/A' > 0.28` strictly: `1/A' = 0.28000392...`. -/
theorem theta_slack : (0.28 : ℝ) < 1 / Ap := by rw [Ap_eq]; norm_num

/-- `t`, `c`, `d` of the transfer: `A' = t·(25/7) + (1-t)·(8/3)` and `tc + (1-t)d = 0`. -/
theorem transfer_params :
    Ap = 379979 / 380000 * (25 / 7) + (1 - 379979 / 380000) * (8 / 3) ∧
    (379979 / 380000 : ℝ) * (33 / 100000) + (1 - 379979 / 380000) * (-4179769 / 700000) = 0 := by
  rw [Ap_eq]; constructor <;> norm_num

/-! ### Numerical facts -/

theorem exp_c_le : exp (33 / 100000 : ℝ) ≤ 1.0003301 := by
  have h := Real.exp_bound (x := (33 / 100000 : ℝ)) (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (n := 3) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  linarith

theorem exp_d_le : exp (-4179769 / 700000 : ℝ) ≤ 0.002555 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 5.97 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-4179769 / 700000 : ℝ) ≤ exp (-5.97) := exp_le_exp.mpr (by norm_num)
  linarith

theorem exp_small_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10000) : exp x ≤ 1.0001001 := by
  have h := Real.exp_bound (x := x) (by rw [abs_of_nonneg h0]; linarith) (n := 2) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  have h2 := (abs_le.mp h).2
  nlinarith

/-- `α = (A'/A) t e^c ≤ 1.00026082`. -/
theorem alpha_le : Ap / (25 / 7) * (379979 / 380000) * exp (33 / 100000) ≤ 1.00026082 := by
  have := exp_c_le
  rw [Ap_eq]
  nlinarith

/-- `β = (A'/B)(1-t) e^d ≤ 1.9 · 10⁻⁷`. -/
theorem beta_le : Ap / (8 / 3) * (1 - 379979 / 380000) * exp (-4179769 / 700000) ≤ 1.9e-7 := by
  have := exp_d_le
  rw [Ap_eq]
  nlinarith

theorem alpha_pos : 0 < Ap / (25 / 7) * (379979 / 380000) * exp (33 / 100000) := by
  rw [Ap_eq]; positivity

theorem beta_pos : 0 < Ap / (8 / 3) * (1 - 379979 / 380000) * exp (-4179769 / 700000) := by
  rw [Ap_eq]; norm_num; positivity

/-- Case 7, (9.29) at `A'`: `e^{-A'·0.04} ≤ 0.8668798`. -/
theorem case7_e1 : exp (-(Ap * 0.04)) ≤ 0.8668798 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 0.142855 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-(Ap * 0.04)) ≤ exp (-0.142855) := exp_le_exp.mpr (by rw [Ap_eq]; norm_num)
  linarith

/-- Case 7, (9.29) at `A'`: `e^{-A'Λ₁} ≥ 0.000175`, `Λ₁ = 2.421`. -/
theorem case7_e2 : (0.000175 : ℝ) ≤ exp (-(Ap * 2.421)) := by
  have h1 := LeanLab.Pintz2018.expneg_lower 4.3232 (by norm_num) (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-8.6464) = exp (-4.3232) ^ 2 := by rw [← exp_nat_mul]; norm_num
  have h3 : exp (-8.6464) ≤ exp (-(Ap * 2.421)) := exp_le_exp.mpr (by rw [Ap_eq]; norm_num)
  have h4 : (0.013229 : ℝ) ≤ exp (-4.3232) := by linarith
  nlinarith

/-- Case 7, (9.27) at `A'`: `e^{-(A' - 8/3)Λ₁} ≤ 0.1118832`. -/
theorem case7_e3 : exp (-((Ap - 8 / 3) * 2.421)) ≤ 0.1118832 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 2.1903 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-((Ap - 8 / 3) * 2.421)) ≤ exp (-2.1903) :=
    exp_le_exp.mpr (by rw [Ap_eq]; norm_num)
  linarith

/-- Case 7 closure in numbers, the analogue of (9.30) at `A'`:
`a² + M(2a + Σb) < 1` for `a ≤ e^{-A'·0.04} - e^{-A'Λ₁}`, `Σb ≤ 15.6 e^{-(A'-8/3)Λ₁}`,
`M ≤ α·0.0715 + β·15.6`. The value is `0.9999857 < 1`; at `A = 25/7` it is `0.9998895`. -/
theorem case7_numbers {a M Sb : ℝ} (ha0 : 0 ≤ a) (hM0 : 0 ≤ M)
    (ha : a ≤ exp (-(Ap * 0.04)) - exp (-(Ap * 2.421)))
    (hSb : Sb ≤ 15.6 * exp (-((Ap - 8 / 3) * 2.421)))
    (hM : M ≤ Ap / (25 / 7) * (379979 / 380000) * exp (33 / 100000) * 0.0715 +
      Ap / (8 / 3) * (1 - 379979 / 380000) * exp (-4179769 / 700000) * 15.6) :
    a ^ 2 + M * (2 * a + Sb) < 1 := by
  have e1 := case7_e1
  have e2 := case7_e2
  have e3 := case7_e3
  have al := alpha_le
  have be := beta_le
  have ha' : a ≤ 0.8667048 := by linarith
  have hSb' : Sb ≤ 1.74537792 := by linarith
  have hM' : M ≤ 0.07152161263 := by linarith
  have hSb0 : 0 ≤ 2 * a + Sb ∨ 2 * a + Sb < 0 := le_or_gt 0 _
  calc a ^ 2 + M * (2 * a + Sb) ≤ 0.8667048 ^ 2 + 0.07152161263 * (2 * 0.8667048 + 1.74537792) := by
        rcases hSb0 with h | h
        · have : M * (2 * a + Sb) ≤ 0.07152161263 * (2 * 0.8667048 + 1.74537792) := by
            apply mul_le_mul hM' (by linarith) h (by norm_num)
          nlinarith
        · nlinarith
    _ < 1 := by norm_num

/-! ### Case 7 at `A'` -/

section Cases
variable {ι κ : Type*}

/-- **Case 7 at `A' = 25/7 - 1/20000`.** CONDITIONAL ON the quoted inputs at `A = 25/7`:
`h928`, (9.28), Lemma 6 in Case 7, `max b_i(25/7, Λ₁) < 0.0715`; `h927`, the Corollary 1 total
behind (9.27), `Σ_j e^{-(8/3) max(λ_j,Λ₁)} ≤ 15.6`; `hsingle` and `hl1`, Tables 4 and 5 of [9]:
one zero `ϱ₁` with `λ₁ ≥ 0.04` and every other zero at `λ ≥ Λ₁ = 2.421`.

Plain math: let classes `i ∈ I` have zeros `λ_j ≤ H`, `j ∈ Z_i`, `H ≥ 2.421`. If the only zero
below `2.421` is `λ₁ ≥ 0.04`, every `b_i` at weight `25/7` and cut `2.421` is at most `0.0715`,
and `Σ_j e^{-(8/3)max(λ_j, 2.421)} ≤ 15.6`, then at weight `A' = 25/7 - 1/20000`,
`S₀ = Σ_i (a_i + b_i)² < 1`. -/
theorem case7_closes {I : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {H : ℝ} {i1 : κ} {j1 : ι}
    (hH : 2.421 ≤ H) (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H) (hi1 : i1 ∈ I) (hj1 : j1 ∈ Z i1)
    (hsingle : ∀ i ∈ I, ∀ j ∈ Z i, lam j < 2.421 → i = i1 ∧ j = j1) (hl1 : 0.04 ≤ lam j1)
    (h928 : ∀ i ∈ I, bS (25 / 7) 2.421 H (Z i) lam ≤ 0.0715)
    (h927 : ∑ i ∈ I, KS (8 / 3) 2.421 (Z i) lam ≤ 15.6) :
    ∑ i ∈ I, (aS Ap 2.421 (Z i) lam + bS Ap 2.421 H (Z i) lam) ^ 2 < 1 := by
  obtain ⟨hAp, hcd⟩ := transfer_params
  have hAp0 : 0 ≤ Ap := by rw [Ap_eq]; norm_num
  have hα := alpha_pos
  have hβ := beta_pos
  set α := Ap / (25 / 7) * (379979 / 380000) * exp (33 / 100000) with hαd
  set β := Ap / (8 / 3) * (1 - 379979 / 380000) * exp (-4179769 / 700000) with hβd
  -- the `a`-sum
  have hasum : ∑ i ∈ I, aS Ap 2.421 (Z i) lam ≤ exp (-(Ap * 0.04)) - exp (-(Ap * 2.421)) := by
    rw [aS_single hi1 hj1 hsingle]
    have : exp (-(Ap * min (lam j1) 2.421)) ≤ exp (-(Ap * 0.04)) :=
      exp_le_exp.mpr (by nlinarith [le_min hl1 (by norm_num : (0.04 : ℝ) ≤ 2.421)])
    linarith
  -- each `b_i` at `A'`
  have hbi : ∀ i ∈ I, bS Ap 2.421 H (Z i) lam ≤ α * 0.0715 + β * 15.6 := by
    intro i hi
    have ht := bS_transfer (A := 25 / 7) (B := 8 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hAp hcd (hZH i hi) hH
    rw [← hαd, ← hβd] at ht
    have hK : bS (8 / 3) 2.421 H (Z i) lam ≤ 15.6 :=
      (bS_le_KS _ _ _ _ _).trans ((single_le_sum (fun i _ => KS_nonneg _ _ (Z i) lam) hi).trans h927)
    have h1 := mul_le_mul_of_nonneg_left (h928 i hi) hα.le
    have h2 := mul_le_mul_of_nonneg_left hK hβ.le
    linarith
  -- the `b`-sum
  have hbsum : ∑ i ∈ I, bS Ap 2.421 H (Z i) lam ≤ 15.6 * exp (-((Ap - 8 / 3) * 2.421)) := by
    calc ∑ i ∈ I, bS Ap 2.421 H (Z i) lam
        ≤ ∑ i ∈ I, exp (-((Ap - 8 / 3) * 2.421)) * KS (8 / 3) 2.421 (Z i) lam :=
          sum_le_sum fun i _ => bS_tail (by rw [Ap_eq]; norm_num) _ _
      _ = exp (-((Ap - 8 / 3) * 2.421)) * ∑ i ∈ I, KS (8 / 3) 2.421 (Z i) lam := by rw [mul_sum]
      _ ≤ exp (-((Ap - 8 / 3) * 2.421)) * 15.6 := mul_le_mul_of_nonneg_left h927 (exp_pos _).le
      _ = _ := by ring
  have hb := LeanLab.Pintz2018.basic_ineq I (fun i => aS Ap 2.421 (Z i) lam)
    (fun i => bS Ap 2.421 H (Z i) lam) (α * 0.0715 + β * 15.6)
    (exp (-(Ap * 0.04)) - exp (-(Ap * 2.421))) (15.6 * exp (-((Ap - 8 / 3) * 2.421)))
    (by positivity) (fun i _ => aS_nonneg hAp0 _ _) (fun i hi => bS_nonneg hAp0 (hZH i hi) hH)
    hbi hasum hbsum
  have ha0 : 0 ≤ exp (-(Ap * 0.04)) - exp (-(Ap * 2.421)) := by
    have : exp (-(Ap * 2.421)) ≤ exp (-(Ap * 0.04)) := exp_le_exp.mpr (by rw [Ap_eq]; norm_num)
    linarith
  have hn := case7_numbers ha0 (by positivity) le_rfl le_rfl le_rfl
  exact lt_of_le_of_lt hb hn

/-- Vacuity instance for `case7_closes`: one class, one zero at `λ₁ = 0.1`, `H = Λ₁`. Every
hypothesis holds, so the theorem is not vacuous. -/
theorem case7_vacuity :
    ∑ _i ∈ ({0} : Finset ℕ), (aS Ap 2.421 ({0} : Finset ℕ) (fun _ => (0.1 : ℝ)) +
      bS Ap 2.421 2.421 ({0} : Finset ℕ) (fun _ => (0.1 : ℝ))) ^ 2 < 1 := by
  have := case7_closes (ι := ℕ) (κ := ℕ) (I := {0}) (Z := fun _ => {0})
    (lam := fun _ => (0.1 : ℝ)) (H := 2.421) (i1 := 0) (j1 := 0) le_rfl
    (by intro _ _ _ _; norm_num) (by simp) (by simp)
    (by intro i hi j hj _; simp_all) (by norm_num)
    (by
      intro i _
      simp only [bS, sum_singleton]
      rw [max_eq_right (by norm_num : (0.1 : ℝ) ≤ 2.421)]
      norm_num)
    (by
      simp only [KS, sum_singleton]
      have : exp (-(8 / 3 * max (0.1 : ℝ) 2.421)) ≤ 1 := exp_le_one_iff.mpr (by
        rw [max_eq_right (by norm_num : (0.1 : ℝ) ≤ 2.421)]; norm_num)
      linarith)
  simpa using this

/-! ### Cases 1 to 6 at `A'` -/

theorem cases16_e1 : exp ((1 / 20000 : ℝ) * 1.311) ≤ 1.0001001 :=
  exp_small_le (by norm_num) (by norm_num)

theorem cases16_e2 : exp (-((Ap - 8 / 3) * 1.311)) ≤ 0.30545 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 1.186 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-((Ap - 8 / 3) * 1.311)) ≤ exp (-1.186) :=
    exp_le_exp.mpr (by rw [Ap_eq]; norm_num)
  linarith

/-- **Cases 1 to 6 at `A' = 25/7 - 1/20000`.** CONDITIONAL ON the quoted inputs at `A = 25/7`:
`h920`, (9.20) from Lemma 7 and (9.18), `Σ_i a_i ≤ 0.622`; Lemma 6, (9.5), as used in
(9.22) to (9.26): `b_i ≤ c*₁ = 0.0722` outside `I₂ ∪ I₃`, `≤ c*₂ = 0.0751` on `I₂`,
`≤ c*₃ = 0.0826` on `I₃`, `|I₂|, |I₃| ≤ 2`; `h96`, the Corollary 1 total of (9.6),
`Σ_j e^{-(8/3) max(λ_j,Λ₀)} ≤ 22.281`.

Plain math: under these, at weight `A'` and cut `Λ₀ = 1.311`, `S₀ = Σ_i (a_i + b_i)² < 0.9835`.
The paper's (9.21) gives `S < 0.9832` at `25/7`. -/
theorem cases1to6_closes {I I2 I3 : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {H : ℝ}
    (hH : 1.311 ≤ H) (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H)
    (h920 : ∑ i ∈ I, aS (25 / 7) 1.311 (Z i) lam ≤ 0.622)
    (h1 : ∀ i ∈ I, i ∉ I2 → i ∉ I3 → bS (25 / 7) 1.311 H (Z i) lam ≤ 0.0722)
    (h2 : ∀ i ∈ I, i ∈ I2 → bS (25 / 7) 1.311 H (Z i) lam ≤ 0.0751)
    (h3 : ∀ i ∈ I, bS (25 / 7) 1.311 H (Z i) lam ≤ 0.0826)
    (hI2 : I2.card ≤ 2) (hI3 : I3.card ≤ 2)
    (h96 : ∑ i ∈ I, KS (8 / 3) 1.311 (Z i) lam ≤ 22.281) :
    ∑ i ∈ I, (aS Ap 1.311 (Z i) lam + bS Ap 1.311 H (Z i) lam) ^ 2 < 0.9835 := by
  obtain ⟨hAp, hcd⟩ := transfer_params
  have hAp0 : 0 ≤ Ap := by rw [Ap_eq]; norm_num
  have hα := alpha_pos
  have hβ := beta_pos
  have hαu := alpha_le
  have hβu := beta_le
  set α := Ap / (25 / 7) * (379979 / 380000) * exp (33 / 100000) with hαd
  set β := Ap / (8 / 3) * (1 - 379979 / 380000) * exp (-4179769 / 700000) with hβd
  have hK : ∀ i ∈ I, bS (8 / 3) 1.311 H (Z i) lam ≤ 22.281 := fun i hi =>
    (bS_le_KS _ _ _ _ _).trans ((single_le_sum (fun i _ => KS_nonneg _ _ (Z i) lam) hi).trans h96)
  have htr : ∀ i ∈ I, ∀ c : ℝ, bS (25 / 7) 1.311 H (Z i) lam ≤ c →
      bS Ap 1.311 H (Z i) lam ≤ α * c + β * 22.281 := by
    intro i hi c hc
    have ht := bS_transfer (A := 25 / 7) (B := 8 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hAp hcd (hZH i hi) hH
    rw [← hαd, ← hβd] at ht
    have := mul_le_mul_of_nonneg_left hc hα.le
    have := mul_le_mul_of_nonneg_left (hK i hi) hβ.le
    linarith
  -- the `a`-sum at `A'`
  have hasum : ∑ i ∈ I, aS Ap 1.311 (Z i) lam ≤ exp ((1 / 20000) * 1.311) * 0.622 := by
    have hs : ∀ i ∈ I, aS Ap 1.311 (Z i) lam ≤ exp ((1 / 20000) * 1.311) *
        aS (25 / 7) 1.311 (Z i) lam := fun i _ => by
      have := aS_scale (A := 25 / 7) (η := 1 / 20000) (Λ := 1.311) (by norm_num) (Z i) lam
      simpa [Ap] using this
    calc ∑ i ∈ I, aS Ap 1.311 (Z i) lam
        ≤ ∑ i ∈ I, exp ((1 / 20000) * 1.311) * aS (25 / 7) 1.311 (Z i) lam := sum_le_sum hs
      _ = exp ((1 / 20000) * 1.311) * ∑ i ∈ I, aS (25 / 7) 1.311 (Z i) lam := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h920 (exp_pos _).le
  -- the `b`-sum at `A'`
  have hbsum : ∑ i ∈ I, bS Ap 1.311 H (Z i) lam ≤ 22.281 * exp (-((Ap - 8 / 3) * 1.311)) := by
    calc ∑ i ∈ I, bS Ap 1.311 H (Z i) lam
        ≤ ∑ i ∈ I, exp (-((Ap - 8 / 3) * 1.311)) * KS (8 / 3) 1.311 (Z i) lam :=
          sum_le_sum fun i _ => bS_tail (by rw [Ap_eq]; norm_num) _ _
      _ = exp (-((Ap - 8 / 3) * 1.311)) * ∑ i ∈ I, KS (8 / 3) 1.311 (Z i) lam := by rw [mul_sum]
      _ ≤ exp (-((Ap - 8 / 3) * 1.311)) * 22.281 := mul_le_mul_of_nonneg_left h96 (exp_pos _).le
      _ = _ := by ring
  have hr := refined_ineq I I2 I3 (fun i => aS Ap 1.311 (Z i) lam)
    (fun i => bS Ap 1.311 H (Z i) lam) (Aa := exp ((1 / 20000) * 1.311) * 0.622)
    (Bb := 22.281 * exp (-((Ap - 8 / 3) * 1.311)))
    (c1 := α * 0.0722 + β * 22.281) (c2 := α * 0.0751 + β * 22.281)
    (c3 := α * 0.0826 + β * 22.281)
    (fun i _ => aS_nonneg hAp0 _ _) (fun i hi => bS_nonneg hAp0 (hZH i hi) hH)
    (by positivity) (by nlinarith) (by nlinarith)
    (fun i hi h2' h3' => htr i hi _ (h1 i hi h2' h3'))
    (fun i hi h2' => htr i hi _ (h2 i hi h2')) (fun i hi => htr i hi _ (h3 i hi)) hI2 hI3
    hasum hbsum
  refine lt_of_le_of_lt hr ?_
  -- numbers: the expression is increasing in `Aa, Bb, α, β ≥ 0`
  have e1 := cases16_e1
  have e2 := cases16_e2
  set x := exp ((1 / 20000 : ℝ) * 1.311)
  set y := exp (-((Ap - 8 / 3) * 1.311))
  have hx0 : 0 ≤ x := (exp_pos _).le
  have hy0 : 0 ≤ y := (exp_pos _).le
  have key : (x * 0.622) ^ 2 + (α * 0.0722 + β * 22.281) * (2 * (x * 0.622) + 22.281 * y) +
      (α * 0.0826 + β * 22.281 - (α * 0.0722 + β * 22.281)) *
        (2 * (x * 0.622) + 2 * (α * 0.0826 + β * 22.281)) +
      (α * 0.0751 + β * 22.281 - (α * 0.0722 + β * 22.281)) * (2 * (α * 0.0751 + β * 22.281)) =
      0.622 ^ 2 * x ^ 2 + (α * 0.0722 + β * 22.281) * (2 * 0.622 * x + 22.281 * y) +
      0.0104 * α * (2 * 0.622 * x + 2 * (α * 0.0826 + β * 22.281)) +
      0.0029 * α * (2 * (α * 0.0751 + β * 22.281)) := by ring
  rw [key]
  calc 0.622 ^ 2 * x ^ 2 + (α * 0.0722 + β * 22.281) * (2 * 0.622 * x + 22.281 * y) +
      0.0104 * α * (2 * 0.622 * x + 2 * (α * 0.0826 + β * 22.281)) +
      0.0029 * α * (2 * (α * 0.0751 + β * 22.281))
      ≤ 0.622 ^ 2 * 1.0001001 ^ 2 + (1.00026082 * 0.0722 + 1.9e-7 * 22.281) *
          (2 * 0.622 * 1.0001001 + 22.281 * 0.30545) +
        0.0104 * 1.00026082 * (2 * 0.622 * 1.0001001 + 2 * (1.00026082 * 0.0826 + 1.9e-7 * 22.281)) +
        0.0029 * 1.00026082 * (2 * (1.00026082 * 0.0751 + 1.9e-7 * 22.281)) := by
        gcongr
    _ < 0.9835 := by norm_num

/-! ### Case 8 at `A'` -/

/-- `e^{-(A'-2)Λ*} ≤ λ₁^{11/7}` when `Λ* ≥ (12/11 - ε) log(1/λ₁)`, `0 < λ₁ ≤ 1`, `ε ≤ 1/100`;
the paper's `ε > 0` is not needed. -/
theorem case8_pow {l Ls ε : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hε : ε ≤ 1 / 100)
    (hLs : (12 / 11 - ε) * log (1 / l) ≤ Ls) :
    exp (-((Ap - 2) * Ls)) ≤ l ^ (11 / 7 : ℝ) := by
  have hlog : 0 ≤ log (1 / l) := log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
  have hA2 : (11 / 7 : ℝ) ≤ (Ap - 2) * (12 / 11 - ε) := by rw [Ap_eq]; nlinarith
  have hA20 : 0 ≤ Ap - 2 := by rw [Ap_eq]; norm_num
  have h1 : 11 / 7 * log (1 / l) ≤ (Ap - 2) * Ls := by
    calc 11 / 7 * log (1 / l) ≤ (Ap - 2) * (12 / 11 - ε) * log (1 / l) :=
          mul_le_mul_of_nonneg_right hA2 hlog
      _ = (Ap - 2) * ((12 / 11 - ε) * log (1 / l)) := by ring
      _ ≤ (Ap - 2) * Ls := mul_le_mul_of_nonneg_left hLs hA20
  rw [rpow_def_of_pos hl0]
  apply exp_le_exp.mpr
  rw [one_div, log_inv] at h1
  linarith

theorem case8_e : exp (-((Ap - 8 / 3) * 3.96)) ≤ 0.02791 := by
  have h1 := LeanLab.Pintz2018.expneg_upper 3.58 (by norm_num)
  simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : exp (-((Ap - 8 / 3) * 3.96)) ≤ exp (-3.58) := exp_le_exp.mpr (by rw [Ap_eq]; norm_num)
  linarith

/-- **Case 8 at `A' = 25/7 - 1/20000`.** CONDITIONAL ON the quoted inputs: Theorem G and Table 5
of [9] as (9.31), one zero `λ₁ ∈ (0, 0.04]` and all others at `λ ≥ Λ*` with
`Λ* ≥ 3.96` and `Λ* ≥ (12/11 - ε) log(1/λ₁)`; Corollary 1 as (9.32), written with the single term
of `ϱ₁` added, whose `max(λ₁, Λ*) = Λ*`: `Σ_j e^{-(8/3)max(λ_j,Λ*)} ≤ 10.4 + e^{-(8/3)Λ*}` and
for each class `Σ_j e^{-2 max(λ_j,Λ*)} ≤ 10.4 + e^{-2Λ*}`.

Plain math: then at weight `A'` and cut `Λ*`, `S₀ = Σ_i (a_i + b_i)² < 1`. -/
theorem case8_closes {I : Finset κ} {Z : κ → Finset ι} {lam : ι → ℝ} {H Ls ε : ℝ} {i1 : κ}
    {j1 : ι} (hLH : Ls ≤ H) (hZH : ∀ i ∈ I, ∀ j ∈ Z i, lam j ≤ H) (hi1 : i1 ∈ I)
    (hj1 : j1 ∈ Z i1) (hsingle : ∀ i ∈ I, ∀ j ∈ Z i, lam j < Ls → i = i1 ∧ j = j1)
    (hl0 : 0 < lam j1) (hl1 : lam j1 ≤ 0.04) (hε : ε ≤ 1 / 100)
    (hLs1 : 3.96 ≤ Ls) (hLs2 : (12 / 11 - ε) * log (1 / lam j1) ≤ Ls)
    (h932a : ∑ i ∈ I, KS (8 / 3) Ls (Z i) lam ≤ 10.4 + exp (-(8 / 3 * Ls)))
    (h932b : ∀ i ∈ I, KS 2 Ls (Z i) lam ≤ 10.4 + exp (-(2 * Ls))) :
    ∑ i ∈ I, (aS Ap Ls (Z i) lam + bS Ap Ls H (Z i) lam) ^ 2 < 1 := by
  set l := lam j1
  have hAp0 : 0 ≤ Ap := by rw [Ap_eq]; norm_num
  have hH : Ls ≤ H := hLH
  -- `a`
  have hasum : ∑ i ∈ I, aS Ap Ls (Z i) lam ≤ exp (-(Ap * l)) := by
    rw [aS_single hi1 hj1 hsingle, min_eq_left (by linarith : l ≤ Ls)]
    linarith [exp_pos (-(Ap * Ls))]
  -- `max b_i`
  have hpow := case8_pow hl0 (by linarith) hε hLs2
  have hm2 : exp (-(2 * Ls)) ≤ 0.01 := by
    have h1 := LeanLab.Pintz2018.expneg_upper 7.92 (by norm_num)
    simp only [LeanLab.Pintz2018.T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
    norm_num at h1
    have : exp (-(2 * Ls)) ≤ exp (-7.92) := exp_le_exp.mpr (by linarith)
    linarith
  have hbi : ∀ i ∈ I, bS Ap Ls H (Z i) lam ≤ 10.41 * l ^ (11 / 7 : ℝ) := by
    intro i hi
    have h1 := bS_tail (A := Ap) (B := 2) (Λ := Ls) (H := H) (by rw [Ap_eq]; norm_num) (Z i) lam
    have h2 := h932b i hi
    have hp0 : 0 ≤ l ^ (11 / 7 : ℝ) := rpow_nonneg hl0.le _
    have he0 := (exp_pos (-((Ap - 2) * Ls))).le
    calc bS Ap Ls H (Z i) lam ≤ exp (-((Ap - 2) * Ls)) * KS 2 Ls (Z i) lam := h1
      _ ≤ l ^ (11 / 7 : ℝ) * 10.41 :=
          mul_le_mul hpow (by linarith) (KS_nonneg _ _ _ _) hp0
      _ = _ := by ring
  -- `Σ b_i`
  have hm83 : exp (-(8 / 3 * Ls)) ≤ 0.01 := by
    have : exp (-(8 / 3 * Ls)) ≤ exp (-(2 * Ls)) := exp_le_exp.mpr (by linarith)
    linarith
  have hbsum : ∑ i ∈ I, bS Ap Ls H (Z i) lam ≤ 0.2906 := by
    have he : exp (-((Ap - 8 / 3) * Ls)) ≤ 0.02791 := by
      have : exp (-((Ap - 8 / 3) * Ls)) ≤ exp (-((Ap - 8 / 3) * 3.96)) :=
        exp_le_exp.mpr (by rw [Ap_eq] at *; nlinarith)
      linarith [case8_e]
    calc ∑ i ∈ I, bS Ap Ls H (Z i) lam
        ≤ ∑ i ∈ I, exp (-((Ap - 8 / 3) * Ls)) * KS (8 / 3) Ls (Z i) lam :=
          sum_le_sum fun i _ => bS_tail (by rw [Ap_eq]; norm_num) _ _
      _ = exp (-((Ap - 8 / 3) * Ls)) * ∑ i ∈ I, KS (8 / 3) Ls (Z i) lam := by rw [mul_sum]
      _ ≤ 0.02791 * 10.41 := mul_le_mul he (by linarith)
          (sum_nonneg fun i _ => KS_nonneg _ _ _ _) (by norm_num)
      _ ≤ 0.2906 := by norm_num
  have hb := LeanLab.Pintz2018.basic_ineq I (fun i => aS Ap Ls (Z i) lam)
    (fun i => bS Ap Ls H (Z i) lam) (10.41 * l ^ (11 / 7 : ℝ)) (exp (-(Ap * l))) 0.2906
    (by positivity) (fun i _ => aS_nonneg hAp0 _ _) (fun i hi => bS_nonneg hAp0 (hZH i hi) hH)
    hbi hasum hbsum
  refine lt_of_le_of_lt hb ?_
  have he1 : exp (-(Ap * l)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hsq : exp (-(Ap * l)) ^ 2 = exp (-(2 * Ap) * l) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hp0 : 0 ≤ l ^ (11 / 7 : ℝ) := rpow_nonneg hl0.le _
  have hc8 := LeanLab.ExceptionalSet.Pintz2018Reduction.case8_A (A := Ap) (l := l)
    (by rw [Ap_eq]; norm_num) hl0 hl1
  have : 10.41 * l ^ (11 / 7 : ℝ) * (2 * exp (-(Ap * l)) + 0.2906) ≤
      2.87 * 10.4 * l ^ (11 / 7 : ℝ) := by nlinarith [(exp_pos (-(Ap * l))).le]
  rw [hsq]
  linarith

end Cases

/-! ### Theorem 1 with strict room -/

/-- CONDITIONAL ON Theorem B and the non-Siegel count at `ϑ' = 1/A' = 0.2800039...`, the level
that `case7_closes`, `cases1to6_closes` and `case8_closes` support: Theorem 1,
`E(X) < X^{0.72}` for large `X`, with the `O_ε` constant of (2.29) absorbed by the strict room
`ϑ' - 0.28 > 3.9 · 10⁻⁶`. Plain math: if `E` restricted to non-Siegel blocks is
`≤ C Y^{1 - 1/A'}`, and Theorem B holds, then `E(X) < X^{0.72}` eventually. -/
theorem pintz_slack {Siegel : ℕ → Prop} {C : ℝ}
    (hB : LeanLab.ExceptionalSet.Pintz2018Reduction.TheoremBInput Siegel)
    (hA : LeanLab.ExceptionalSet.Pintz2018Reduction.NonSiegelInput Siegel (1 / Ap) C) :
    LeanLab.ExceptionalSet.EventuallyBelow 0.72 :=
  LeanLab.ExceptionalSet.Pintz2018Reduction.pintz_of_inputs theta_slack hB hA

end LeanLab.ExceptionalSet.Pintz2018Slack
