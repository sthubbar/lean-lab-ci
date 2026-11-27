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

/-! ### Private helpers for the two leaves -/

namespace Dual1122bAux

lemma eC_add1122b (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma eC_int1122b (m : ℤ) : eC m = 1 := by
  unfold eC
  have : 2 * Real.pi * Complex.I * ((m : ℝ) : ℂ) = m * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma norm_eC1122b (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : 2 * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma eC_nat_mul1122b (γ : ℝ) (k : ℕ) : eC (γ * k) = eC γ ^ k := by
  unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma abs_sin_ge1122b (t : ℝ) (ht : |t| ≤ 1 / 2) : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
  have hπ := Real.pi_pos
  have h1 : |Real.sin (Real.pi * t)| = Real.sin (Real.pi * |t|) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [abs_of_nonneg h])
    · rw [abs_of_nonpos h, mul_neg, Real.sin_neg, abs_of_nonpos]
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith) (by nlinarith [abs_of_nonpos h])
  rw [h1]
  have := Real.mul_le_sin (x := Real.pi * |t|) (by positivity) (by nlinarith)
  calc 2 * |t| = 2 / Real.pi * (Real.pi * |t|) := by field_simp
    _ ≤ _ := this

lemma norm_eC_sub_one1122b (t : ℝ) (ht : |t| ≤ 1 / 2) : 4 * |t| ≤ ‖eC t - 1‖ := by
  have : eC t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold eC; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [this]
  linarith [abs_sin_ge1122b t ht]

lemma geom_interval_Icc1122b (a b : ℕ) (γ : ℝ) (m : ℤ) (hm : |γ - m| ≤ 1 / 2) :
    ‖∑ n ∈ Icc a b, eC (γ * n)‖ * (2 * |γ - m|) ≤ 1 := by
  set t := γ - m with htdef
  by_cases ht : t = 0
  · rw [ht]; simp
  have hz : eC γ = eC t := by
    have : γ = t + m := by rw [htdef]; ring
    rw [this, eC_add1122b, eC_int1122b, mul_one]
  have h4 := norm_eC_sub_one1122b t hm
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hz1 : eC γ ≠ 1 := by
    intro h; rw [hz] at h; rw [h, sub_self, norm_zero] at h4; linarith
  have hsum : ∑ n ∈ Icc a b, eC (γ * n) = eC (γ * a) * ∑ k ∈ range (b + 1 - a), eC γ ^ k := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← eC_nat_mul1122b, ← eC_add1122b]; congr 1; push_cast; ring
  rw [hsum, norm_mul, norm_eC1122b, one_mul, geom_sum_eq hz1, norm_div]
  have hnum : ‖eC γ ^ (b + 1 - a) - 1‖ ≤ 2 := by
    calc _ ≤ ‖eC γ ^ (b + 1 - a)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_eC1122b]; norm_num
  rw [hz]
  have hden : 0 < ‖eC t - 1‖ := by linarith
  rw [div_mul_eq_mul_div, div_le_one hden]
  rw [hz] at hnum
  nlinarith

lemma card_near1122b (Q : ℕ) (β r : ℝ) (hr : 0 ≤ r) (A : Finset ℕ) (hA : A ⊆ range Q)
    (hnear : ∀ a ∈ A, |(a : ℝ) - Q * (round ((a : ℝ) / Q - β) : ℝ) - Q * β| ≤ r) :
    (#A : ℝ) ≤ 2 * r + 1 := by
  set f : ℕ → ℤ := fun a => (a : ℤ) - Q * round ((a : ℝ) / Q - β) with hf
  set lo : ℤ := ⌈(Q : ℝ) * β - r⌉
  set hi : ℤ := ⌊(Q : ℝ) * β + r⌋
  have hmaps : ∀ a ∈ A, f a ∈ Icc lo hi := by
    intro a ha
    have h := hnear a ha
    rw [abs_le] at h
    have hfa : ((f a : ℤ) : ℝ) = (a : ℝ) - Q * (round ((a : ℝ) / Q - β) : ℝ) := by
      simp [hf]
    rw [Finset.mem_Icc]
    constructor
    · apply Int.ceil_le.mpr; rw [hfa]; linarith
    · apply Int.le_floor.mpr; rw [hfa]; linarith
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp (hA ha)
    have hb' := Finset.mem_range.mp (hA hb)
    simp only [hf] at hab
    have h1 : (a : ℤ) = b + Q * (round ((a : ℝ) / Q - β) - round ((b : ℝ) / Q - β)) := by
      linarith
    have h2 : (a : ℤ) % Q = (b : ℤ) % Q := by
      rw [h1, Int.add_mul_emod_self_left]
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha'),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb')] at h2
    exact_mod_cast h2
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Int.card_Icc] at hcard
  have hcR : (#A : ℝ) ≤ ((hi + 1 - lo).toNat : ℝ) := by exact_mod_cast hcard
  have hlo : (Q : ℝ) * β - r ≤ lo := Int.le_ceil _
  have hhi : (hi : ℝ) ≤ Q * β + r := Int.floor_le _
  rcases le_or_gt 0 (hi + 1 - lo) with h | h
  · have : ((hi + 1 - lo).toNat : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [this] at hcR; push_cast at hcR; linarith
  · rw [Int.toNat_of_nonpos h.le] at hcR; simp at hcR; rw [hcR]; simp; linarith

end Dual1122bAux

/-- LEAF: the geometric sum bound over an interval, the first step of the dual count in
Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class EASY. For `|γ - m| ≤ 1/2`,
`|∑_{n ∈ S} e(γ n)| ≤ 1/|sin π γ| ≤ 1/(2 |γ - m|)`. -/
theorem leaf_geometric_interval : ∀ S : Finset ℕ,
    (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ γ : ℝ, ∀ m : ℤ, |γ - m| ≤ 1 / 2 →
      ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - m|) ≤ 1 := by
  intro S hS γ m hm
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; simp
  have hInt : S = Icc (S.min' h) (S.max' h) := by
    ext y; constructor
    · intro hy; exact Finset.mem_Icc.mpr ⟨S.min'_le y hy, S.le_max' y hy⟩
    · intro hy; rw [Finset.mem_Icc] at hy
      exact hS _ (S.min'_mem h) _ (S.max'_mem h) y hy.1 hy.2
  rw [hInt]; exact Dual1122bAux.geom_interval_Icc1122b _ _ γ m hm

/-- LEAF: the count of the `Q` frequencies `a/Q - β`, spaced `1/Q` apart modulo one, the second
step of the dual count in Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class MEDIUM.
`∑_{a < Q} min(N, 1/(2 ‖a/Q - β‖)) ≤ 2N + Q (1 + log Q)`, at most `K (N + Q √N)` once
`6 Q² ≤ N`. -/
theorem leaf_dual_count : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N → ∀ β : ℝ,
    ∀ g : ℕ → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ N) →
    (∀ a : ℕ, ∀ m : ℤ, |(a : ℝ) / Q - β - m| ≤ 1 / 2 → g a * (2 * |(a : ℝ) / Q - β - m|) ≤ 1) →
    ∑ a ∈ range Q, g a ≤ K * (N + Q * Real.sqrt N) := by
  refine ⟨3, by norm_num, fun N Q hQ hNQ β g hg hdual => ?_⟩
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by nlinarith
    exact_mod_cast this
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  set s := Real.sqrt N with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hNpos
  have hss : s * s = N := Real.mul_self_sqrt hNpos.le
  set t : ℕ → ℝ := fun a => (a : ℝ) / Q - β - (round ((a : ℝ) / Q - β) : ℝ) with ht
  have htb : ∀ a, |t a| ≤ 1 / 2 := fun a => abs_sub_round _
  have hgt : ∀ a, g a * (2 * |t a|) ≤ 1 := fun a => hdual a _ (htb a)
  set A := (range Q).filter (fun a => |t a| * s ≤ 1) with hA
  rw [← Finset.sum_filter_add_sum_filter_not (range Q) (fun a => |t a| * s ≤ 1)]
  have hnear : ∑ a ∈ A, g a ≤ (2 * (Q / s) + 1) * N := by
    have hc : (#A : ℝ) ≤ 2 * (Q / s) + 1 := by
      apply Dual1122bAux.card_near1122b Q β (Q / s) (by positivity) A (Finset.filter_subset _ _)
      intro a ha
      have h := (Finset.mem_filter.mp ha).2
      have heq : (a : ℝ) - Q * (round ((a : ℝ) / Q - β) : ℝ) - Q * β = Q * t a := by
        simp only [ht]; field_simp; ring
      rw [heq, abs_mul, abs_of_pos hQpos, le_div_iff₀ hspos]
      nlinarith
    calc ∑ a ∈ A, g a ≤ ∑ a ∈ A, (N : ℝ) := Finset.sum_le_sum fun a _ => (hg a).2
      _ = #A * N := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hNpos.le
  have hfar : ∑ a ∈ (range Q).filter (fun a => ¬ |t a| * s ≤ 1), g a ≤ Q * (s / 2) := by
    calc _ ≤ ∑ a ∈ (range Q).filter (fun a => ¬ |t a| * s ≤ 1), s / 2 := by
          refine Finset.sum_le_sum fun a ha => ?_
          have h := not_le.mp (Finset.mem_filter.mp ha).2
          have h1 := hgt a
          have h0 := (hg a).1
          have : g a * 2 ≤ s := by nlinarith
          linarith
      _ = #((range Q).filter (fun a => ¬ |t a| * s ≤ 1)) * (s / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Q * (s / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := Finset.card_filter_le (range Q) (fun a => ¬ |t a| * s ≤ 1)
          rw [Finset.card_range] at this
          exact_mod_cast this
  have h2 : (2 * (Q / s) + 1) * N = 2 * Q * s + N := by
    rw [← hss]; field_simp
  rw [h2] at hnear
  have : 0 ≤ (Q : ℝ) * s := by positivity
  linarith

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
