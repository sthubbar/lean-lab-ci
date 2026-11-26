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
  refine ⟨3, by norm_num, fun N Q hQ hNQ β g hg hgd => ?_⟩
  have hN : 0 < N := by nlinarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  set s := Real.sqrt N with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hNr
  have hss : s * s = N := Real.mul_self_sqrt hNr.le
  set r : ℕ → ℤ := fun a => round ((a : ℝ) / Q - β) with hr
  set A := (range Q).filter (fun a : ℕ => |(a : ℝ) / Q - β - r a| < 1 / (2 * s)) with hA
  -- the far frequencies
  have hfar : ∀ a ∈ (range Q).filter (fun a : ℕ => ¬ |(a : ℝ) / Q - β - r a| < 1 / (2 * s)),
      g a ≤ s := by
    intro a ha
    rw [mem_filter, not_lt] at ha
    have hh : |(a : ℝ) / Q - β - r a| ≤ 1 / 2 := abs_sub_round _
    have h1 := hgd a (r a) hh
    have h2 : 0 < 2 * |(a : ℝ) / Q - β - r a| := by
      have : 0 < 1 / (2 * s) := by positivity
      linarith
    have h3 : 1 / s ≤ 2 * |(a : ℝ) / Q - β - r a| := by
      have := ha.2
      rw [div_le_iff₀ (by positivity)] at this
      rw [div_le_iff₀ hs0]; linarith
    have h4 : g a * (1 / s) ≤ 1 :=
      (mul_le_mul_of_nonneg_left h3 (hg a).1).trans h1
    rwa [mul_one_div, div_le_one hs0] at h4
  -- the near frequencies are few
  set k : ℕ → ℤ := fun a => (a : ℤ) - Q * r a with hk
  have hkinj : Set.InjOn k (A : Set ℕ) := by
    intro a ha a' ha' he
    simp only [hA, coe_filter, mem_range, Set.mem_ofPred_eq] at ha ha'
    simp only [hk] at he
    have hd : ((a : ℤ) - a') = Q * (r a - r a') := by linarith
    have hQz : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
    have ha1 : (a : ℤ) < Q := by exact_mod_cast ha.1
    have ha2 : (a' : ℤ) < Q := by exact_mod_cast ha'.1
    have hd0 : r a - r a' = 0 := by
      rcases lt_trichotomy (r a - r a') 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hd0, mul_zero] at hd
    exact_mod_cast (sub_eq_zero.mp hd)
  set L : ℝ := Q / (2 * s) with hL
  have hsub : A.image k ⊆ Icc ⌈Q * β - L⌉ ⌊Q * β + L⌋ := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hA, mem_filter] at ha
    have hlt := ha.2
    have e : (a : ℝ) / Q - β - r a = ((k a : ℝ) - Q * β) / Q := by
      simp only [hk]; push_cast; field_simp; ring
    rw [e, abs_div, abs_of_pos hQr, div_lt_iff₀ hQr] at hlt
    have hlt' : |(k a : ℝ) - Q * β| < L := by
      rw [hL]; calc _ < 1 / (2 * s) * Q := hlt
        _ = Q / (2 * s) := by ring
    rw [abs_lt] at hlt'
    rw [mem_Icc]
    constructor
    · rw [Int.ceil_le]; linarith
    · rw [Int.le_floor]; linarith
  have hcard : (A.card : ℝ) ≤ 2 * L + 1 := by
    have h1 : A.card = (A.image k).card := (card_image_of_injOn hkinj).symm
    have h2 := card_le_card hsub
    rw [Int.card_Icc] at h2
    have h3 : (A.card : ℤ) ≤ max (⌊Q * β + L⌋ + 1 - ⌈Q * β - L⌉) 0 := by
      rw [← Int.toNat_eq_max]; omega
    have h4 : ((⌊Q * β + L⌋ + 1 - ⌈Q * β - L⌉ : ℤ) : ℝ) ≤ 2 * L + 1 := by
      push_cast
      have := Int.floor_le (Q * β + L)
      have := Int.le_ceil (Q * β - L)
      linarith
    have hL0 : 0 ≤ L := by positivity
    have h5 : (A.card : ℝ) ≤ max (((⌊Q * β + L⌋ + 1 - ⌈Q * β - L⌉ : ℤ)) : ℝ) 0 := by
      have := (Int.cast_le (R := ℝ)).mpr h3
      rw [Int.cast_max, Int.cast_zero] at this
      exact_mod_cast this
    exact h5.trans (max_le h4 (by linarith))
  have hsplit := (sum_filter_add_sum_filter_not (range Q)
    (fun a : ℕ => |(a : ℝ) / Q - β - r a| < 1 / (2 * s)) g).symm
  have hnear : ∑ a ∈ A, g a ≤ A.card * (N : ℝ) := by
    have := sum_le_card_nsmul A g (N : ℝ) (fun a _ => (hg a).2)
    rwa [nsmul_eq_mul] at this
  have hfar' : ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ |(a : ℝ) / Q - β - r a| < 1 / (2 * s)), g a
      ≤ Q * s := by
    have := sum_le_card_nsmul _ g s hfar
    rw [nsmul_eq_mul] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hs0.le)
    have := card_filter_le (range Q) (fun a : ℕ => ¬ |(a : ℝ) / Q - β - r a| < 1 / (2 * s))
    rw [card_range] at this
    exact_mod_cast this
  have hLN : 2 * L * N = Q * s := by
    rw [hL, ← hss]; field_simp
  rw [hsplit]
  have hNn : (0 : ℝ) ≤ N := hNr.le
  nlinarith [mul_le_mul_of_nonneg_right hcard hNn]

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
