/-
AI-written Lean code, Claude, 2026-10-19, PC run 20261019T1703Z-20733, unit U-1093, T3, route R-5070.
Closes the gap the U-1088 faithfulness check found in R5070Cheb2D.lean: `certificate_sound` was
proved for an abstract weight w, and the step to the real data D N j k was not in Lean.

* `log_eq_sum`: log a = Σ_{d ≤ N, d ∣ a} Λ(d) for 1 ≤ a ≤ N, from Mathlib's `vonMangoldt_sum`.
* `D_eq_Dw`: D N j k = D_w(j, k) with w(d, e) = Λ(d) Λ(e) on S = [1, N]², for j, k ≥ 1, since
  log a · log b = Σ_{d ∣ a, e ∣ b} Λ(d) Λ(e) and #{u + v = N : jd ∣ u, ke ∣ v, u, v ≥ 1} = R(jd, ke).
* `G_eq_Gw`: G N = G_w for the same w.
* `goldbach_ge_certificate`: so for any finite certificate c on pairs j, k ≥ 1 whose response is
  at most [d + e = N] on [1, N]², G(N) ≥ Σ c_jk D(N, j, k), the sentence ROUTES R-5070 states.
The barrier `certificate_le_zero_of_fake` of R5070Cheb2D still applies: such certificates cannot
see N when a nonnegative fake weight with the same data exists. KNOWN mathematics, Möbius and
divisor bookkeeping. Goldbach is OPEN.
-/
import LeanLab.Routes.R5070Cheb2D

open Finset ArithmeticFunction

noncomputable section
namespace LeanLab.Routes.R5070

/-- log a = Σ_{d ∈ [1, N], d ∣ a} Λ(d) for 1 ≤ a ≤ N. -/
lemma log_eq_sum {a N : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) :
    Real.log a = ∑ d ∈ Icc 1 N, if d ∣ a then Λ d else 0 := by
  rw [← vonMangoldt_sum, ← sum_filter]
  apply sum_subset
  · intro d hd
    rw [Nat.mem_divisors] at hd
    rw [mem_filter, mem_Icc]
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 ha, (Nat.le_of_dvd ha hd.1).trans haN⟩, hd.1⟩
  · intro d hd hnot
    rw [mem_filter] at hd
    exact absurd (Nat.mem_divisors.mpr ⟨hd.2, by omega⟩) hnot

/-- The indicator of a point x of the antidiagonal for the pair (d, e). -/
def ind (j k : ℕ) (x : ℕ × ℕ) (p : ℕ × ℕ) : Prop :=
  1 ≤ x.1 ∧ 1 ≤ x.2 ∧ j * p.1 ∣ x.1 ∧ k * p.2 ∣ x.2

instance (j k : ℕ) (x p : ℕ × ℕ) : Decidable (ind j k x p) := by unfold ind; infer_instance

/-- Pointwise expansion of a term of D. -/
lemma term_eq {N j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) {x : ℕ × ℕ} (hx : x.1 + x.2 = N) :
    (if j ∣ x.1 ∧ k ∣ x.2 then
      Real.log ((x.1 / j : ℕ) : ℝ) * Real.log ((x.2 / k : ℕ) : ℝ) else 0) =
    ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, if ind j k x p then Λ p.1 * Λ p.2 else 0 := by
  by_cases h : j ∣ x.1 ∧ k ∣ x.2
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := h
    by_cases hx1 : 1 ≤ x.1
    · by_cases hx2 : 1 ≤ x.2
      · have ha : 1 ≤ x.1 / j := Nat.div_pos (Nat.le_of_dvd hx1 h1) hj
        have hb : 1 ≤ x.2 / k := Nat.div_pos (Nat.le_of_dvd hx2 h2) hk
        have haN : x.1 / j ≤ N := (Nat.div_le_self _ _).trans (by omega)
        have hbN : x.2 / k ≤ N := (Nat.div_le_self _ _).trans (by omega)
        rw [log_eq_sum ha haN, log_eq_sum hb hbN, sum_mul_sum, sum_product]
        apply sum_congr rfl; intro d _; apply sum_congr rfl; intro e _
        simp only [ind, Nat.dvd_div_iff_mul_dvd h1, Nat.dvd_div_iff_mul_dvd h2]
        by_cases hd : j * d ∣ x.1 <;> by_cases he : k * e ∣ x.2 <;> simp [hd, he, hx1, hx2]
      · have : x.2 = 0 := by omega
        rw [this]; simp only [Nat.zero_div, Nat.cast_zero, Real.log_zero, mul_zero]
        symm; apply sum_eq_zero; intro p _; simp [ind, hx2]
    · have : x.1 = 0 := by omega
      rw [this]; simp only [Nat.zero_div, Nat.cast_zero, Real.log_zero, zero_mul]
      symm; apply sum_eq_zero; intro p _; simp [ind, hx1]
  · rw [if_neg h]
    symm; apply sum_eq_zero; intro p _
    rw [if_neg]
    rintro ⟨-, -, hd, he⟩
    exact h ⟨(Dvd.intro _ rfl).trans hd, (Dvd.intro _ rfl).trans he⟩

/-- The count of antidiagonal points for (d, e) is R(jd, ke). -/
lemma count_eq {N a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((antidiagonal N).filter (fun x => 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ a ∣ x.1 ∧ b ∣ x.2)).card = R N a b := by
  unfold R
  symm
  apply card_bij (fun p _ => (a * p.1, b * p.2))
  · intro p hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal]
    refine ⟨hp.2, ?_, ?_, Dvd.intro _ rfl, Dvd.intro _ rfl⟩ <;> nlinarith [hp.1.1.1, hp.1.2.1]
  · intro p hp q hq h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left ha h.1) (Nat.eq_of_mul_eq_mul_left hb h.2)
  · intro x hx
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at hx
    obtain ⟨hsum, h1, h2, ⟨m, hm⟩, ⟨n, hn⟩⟩ := hx
    refine ⟨(m, n), ?_, Prod.ext hm.symm hn.symm⟩
    simp only [mem_filter, mem_product, mem_Icc]
    have hm1 : 1 ≤ m := by rcases Nat.eq_zero_or_pos m with h | h <;> [simp [h] at hm; exact h] <;> omega
    have hn1 : 1 ≤ n := by rcases Nat.eq_zero_or_pos n with h | h <;> [simp [h] at hn; exact h] <;> omega
    refine ⟨⟨⟨hm1, ?_⟩, hn1, ?_⟩, by rw [← hm, ← hn]; exact hsum⟩ <;> nlinarith

/-- The Goldbach weight w(d, e) = Λ(d) Λ(e). -/
def wL (p : ℕ × ℕ) : ℝ := Λ p.1 * Λ p.2

/-- **D N j k is the data of w = Λ ⊗ Λ on [1, N]².** -/
theorem D_eq_Dw (N j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    D N j k = Dw N (Icc 1 N ×ˢ Icc 1 N) wL (j, k) := by
  unfold D Dw
  rw [sum_congr rfl (fun x hx => term_eq hj hk (HasAntidiagonal.mem_antidiagonal.mp hx))]
  rw [sum_comm]
  apply sum_congr rfl; intro p hp
  simp only [mem_product, mem_Icc] at hp
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  unfold wL
  congr 1
  have := count_eq (N := N) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)) :
    1 ≤ j * p.1) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)) : 1 ≤ k * p.2)
  simp only [ind]
  exact_mod_cast this

/-- **G N is the Goldbach mass of w = Λ ⊗ Λ on [1, N]².** -/
theorem G_eq_Gw (N : ℕ) : G N = Gw N (Icc 1 N ×ˢ Icc 1 N) wL := by
  unfold G Gw wL
  rw [← sum_filter]
  have hset : (Icc 1 N ×ˢ Icc 1 N).filter (fun x : ℕ × ℕ => x.1 + x.2 = N) =
      (antidiagonal N).filter (fun x : ℕ × ℕ => x.1 ≠ 0 ∧ x.2 ≠ 0) := by
    ext x
    simp only [mem_filter, mem_product, mem_Icc, HasAntidiagonal.mem_antidiagonal]
    omega
  rw [hset, sum_filter]
  apply sum_congr rfl; intro x _
  split_ifs with h
  · rfl
  · rcases not_and_or.mp h with h1 | h1
    · simp [not_not.mp h1]
    · simp [not_not.mp h1]

/-- **Certificate bound for the real Goldbach count**, the ROUTES R-5070 sentence. -/
theorem goldbach_ge_certificate (N : ℕ) (P : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℝ)
    (hP : ∀ q ∈ P, 1 ≤ q.1 ∧ 1 ≤ q.2)
    (hU : ∀ x ∈ Icc 1 N ×ˢ Icc 1 N, U N P c x.1 x.2 ≤ if x.1 + x.2 = N then 1 else 0) :
    ∑ q ∈ P, c q * D N q.1 q.2 ≤ G N := by
  rw [G_eq_Gw, sum_congr rfl (fun q hq => by rw [D_eq_Dw N q.1 q.2 (hP q hq).1 (hP q hq).2])]
  exact certificate_sound N P _ c wL
    (fun x _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) hU

/-- Vacuity: the hypotheses of `goldbach_ge_certificate` hold for P = {(1, 1)}, c = 0. -/
theorem certificate_vacuity (N : ℕ) : (∀ q ∈ ({(1, 1)} : Finset (ℕ × ℕ)), 1 ≤ q.1 ∧ 1 ≤ q.2) ∧
    ∀ x ∈ Icc 1 N ×ˢ Icc 1 N, U N {(1, 1)} (fun _ => 0) x.1 x.2 ≤ if x.1 + x.2 = N then 1 else 0 := by
  refine ⟨by simp, fun x _ => ?_⟩
  simp only [U, sum_singleton, zero_mul]
  split_ifs <;> norm_num

end LeanLab.Routes.R5070
