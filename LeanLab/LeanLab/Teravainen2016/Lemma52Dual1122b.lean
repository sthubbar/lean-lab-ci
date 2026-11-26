/-
P0076 J. Teräväinen, arXiv 1611.08585, Lemma 5.2, page 18, quoting Matomäki and Shao Lemma 7.4.
The leaf `twisted_interval_bound` of `Lemma52Split1122b` split into the two standard steps of its
proof: the geometric sum bound `|∑_{n ∈ S} e(γ n)| ≤ 1 / (2 ‖γ‖)` over an interval, and the count
of `Q` frequencies spaced `1/Q` apart, `∑_{a < Q} min(N, 1/(2 ‖a/Q - β‖)) ≪ N + Q √N`.
AI wrote this Lean code, Claude, session CLOUD-S69, burst-20261122. Checked only by the Lean
kernel. The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.Lemma52Split1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: the geometric sum bound over an interval, the first step of the dual count in
Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class EASY. For `|γ - m| ≤ 1/2`,
`|∑_{n ∈ S} e(γ n)| ≤ 1/|sin π γ| ≤ 1/(2 |γ - m|)`. -/
theorem leaf_geometric_interval : ∀ S : Finset ℕ,
    (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ γ : ℝ, ∀ m : ℤ, |γ - m| ≤ 1 / 2 →
      ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - m|) ≤ 1 := by
  intro S hS γ m hγ
  set δ := γ - m with hδ
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  rcases eq_or_ne δ 0 with h0 | h0
  · rw [h0]; simp
  set z : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * γ : ℝ) : ℂ)) with hz
  have hpow : ∀ n : ℕ, eC (γ * n) = z ^ n := by
    intro n; unfold eC; rw [hz, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hsin : ‖z - 1‖ = 2 * |Real.sin (Real.pi * δ)| := by
    rw [hz, Complex.norm_exp_I_mul_ofReal_sub_one]
    have : 2 * Real.pi * γ / 2 = Real.pi * δ + m * Real.pi := by rw [hδ]; ring
    rw [this, Real.sin_add_int_mul_pi, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg_one_zpow, one_mul]
    norm_num
  have hjordan : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
    have hpi := Real.pi_pos
    have h1 : 0 ≤ Real.pi * |δ| := by positivity
    have h2 : Real.pi * |δ| ≤ Real.pi / 2 := by nlinarith
    have hj := Real.mul_le_sin h1 h2
    have e : 2 / Real.pi * (Real.pi * |δ|) = 2 * |δ| := by field_simp
    rw [e] at hj
    rcases le_total 0 δ with hd | hd
    · rw [abs_of_nonneg hd] at hj ⊢
      exact hj.trans (le_abs_self _)
    · rw [abs_of_nonpos hd] at hj ⊢
      rw [show Real.pi * -δ = -(Real.pi * δ) by ring, Real.sin_neg] at hj
      exact hj.trans (neg_le_abs _)
  have hδpos : 0 < |δ| := abs_pos.mpr h0
  have hz1 : z ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hsin; linarith
  have hznorm : ‖z‖ = 1 := by rw [hz]; exact Complex.norm_exp_I_mul_ofReal _
  set a := S.min' hne
  set b := S.max' hne
  have hSI : S = Ico a (b + 1) := by
    ext x; rw [mem_Ico]; constructor
    · intro hx; exact ⟨S.min'_le x hx, Nat.lt_succ_of_le (S.le_max' x hx)⟩
    · intro hx; exact hS a (S.min'_mem hne) b (S.max'_mem hne) x hx.1 (Nat.le_of_lt_succ hx.2)
  have hab : a ≤ b + 1 := by
    have := S.min'_le_max' hne; omega
  have hsum : ∑ n ∈ S, eC (γ * n) = (z ^ (b + 1) - z ^ a) / (z - 1) := by
    rw [sum_congr rfl fun n _ => hpow n, hSI, geom_sum_Ico hz1 hab]
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hnum : ‖z ^ (b + 1) - z ^ a‖ ≤ 2 := by
    calc _ ≤ ‖z ^ (b + 1)‖ + ‖z ^ a‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, hznorm]; norm_num
  rw [hsum, norm_div]
  calc ‖z ^ (b + 1) - z ^ a‖ / ‖z - 1‖ * (2 * |δ|) ≤ 2 / ‖z - 1‖ * (2 * |δ|) := by
        gcongr
    _ ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one hpos, hsin]; linarith

/-- LEAF: the count of the `Q` frequencies `a/Q - β`, spaced `1/Q` apart modulo one, the second
step of the dual count in Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class MEDIUM.
`∑_{a < Q} min(N, 1/(2 ‖a/Q - β‖)) ≤ 2N + Q (1 + log Q)`, at most `K (N + Q √N)` once
`6 Q² ≤ N`. -/
theorem leaf_dual_count : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N → ∀ β : ℝ,
    ∀ g : ℕ → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ N) →
    (∀ a : ℕ, ∀ m : ℤ, |(a : ℝ) / Q - β - m| ≤ 1 / 2 → g a * (2 * |(a : ℝ) / Q - β - m|) ≤ 1) →
    ∑ a ∈ range Q, g a ≤ K * (N + Q * Real.sqrt N) := by
  sorry

/-- `twisted_interval_bound` from the two leaves. -/
theorem twisted_interval_bound_of_leaves : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
    ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
      K * (N + Q * Real.sqrt N) := by
  obtain ⟨K, hK, hKb⟩ := leaf_dual_count
  refine ⟨K, hK, fun N Q hQ hNQ S hS hconv β => ?_⟩
  refine hKb N Q hQ hNQ β (fun a => ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖) (fun a => ?_)
    (fun a m hm => leaf_geometric_interval S hconv _ m hm)
  refine ⟨norm_nonneg _, ?_⟩
  calc ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤ ∑ n ∈ S, ‖eC (((a : ℝ) / Q - β) * n)‖ :=
        norm_sum_le _ _
    _ = #S := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        unfold eC
        rw [Complex.norm_exp]
        have h : (2 * (Real.pi : ℂ) * Complex.I * ((((a : ℝ) / Q - β) * n : ℝ) : ℂ)).re = 0 := by
          simp
        rw [h, Real.exp_zero, Nat.cast_one]
    _ ≤ N := by
        have := Finset.card_le_card hS
        rw [Finset.card_range] at this
        exact_mod_cast this

theorem twisted_interval_bound_twin :
    type_of% @LeanLab.Teravainen2016.twisted_interval_bound :=
  twisted_interval_bound_of_leaves

end LeanLab.Teravainen2016
