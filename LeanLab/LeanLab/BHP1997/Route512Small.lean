/-
P0069 Baker Harman Pintz 1997, Section 2, page 8, display 2.8: the small-divisor
mean square estimate on K = [x, x + H],
  Σ_{N ∈ K} (Σ_{d | N, d ≤ P} d/(φ(d) P))² ≪ H ℒ^{-A-7},  P = ℒ^{2D}.
This file proves the printed bound 2.8 in raw form, for every interval length
H = x^h with 0 < h, with no reference to the 512 definitions, so that Decomp512a
can import it.

NOTE on faithfulness. Only the outer bound of 2.8 is proved here, by an elementary
path that may differ from the one the paper has in mind: extend the divisor sum to
all d ≤ P, expand the square, swap the order of summation and count the multiples of
the larger of two divisors in K, which is `small_part512` of Route512Large. That
leaves 2 H (Σ_{d ≤ P} d^{1/2}/(φ(d) P))². With 1/φ(d) ≪ d^{-3/4} each term is at
most K d^{-1/4}/P, and d^{-1/4} is at most 1 for d ≤ P^{1/2} and at most P^{-1/8}
above, so the inner sum is at most 2 K P^{-1/8}. The price is the threshold
D₀ = 2A + 14, the same as in Route512Large.

AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512Large

namespace LeanLab.BHP1997.Route512
open Finset

/-- P0069 page 8 display 2.8, the weighted divisor sum: for `P ≥ 1` and `1/φ(d) ≤ K d^{-3/4}`,
`Σ_{1 ≤ d ≤ P} d/(φ(d) P) d^{-1/2} ≤ 2 K P^{-1/8}`. -/
theorem small_weight_sum_le512 (K : ℝ) (hK : 0 < K)
    (hKb : ∀ d : ℕ, 0 < d → 1 / (Nat.totient d : ℝ) ≤ K * (d : ℝ) ^ (-(3 / 4) : ℝ))
    (P : ℝ) (hP1 : 1 ≤ P) :
    ∑ d ∈ Finset.Icc 1 ⌊P⌋₊,
      (d : ℝ) / (Nat.totient d : ℝ) / P * (d : ℝ) ^ (-(1 / 2) : ℝ) ≤
        2 * K * P ^ (-(1 / 8) : ℝ) := by
  have hP0 : 0 < P := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S = Finset.Icc 1 ⌊P⌋₊ := ⟨_, rfl⟩
  have hSmem : ∀ d : ℕ, d ∈ S ↔ 1 ≤ d ∧ (d : ℝ) ≤ P := by
    intro d
    rw [hSdef, Finset.mem_Icc, Nat.le_floor_iff hP0.le]
  rw [← hSdef]
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = P ^ (-(1 / 8) : ℝ) := ⟨_, rfl⟩
  rw [← hRdef]
  have hR0 : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos hP0 _
  have hQ0 : 0 < P ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hP0 _
  have hQR : (P ^ (1 / 2 : ℝ)) ^ (-(1 / 4) : ℝ) = R := by
    rw [hRdef, ← Real.rpow_mul hP0.le]; norm_num
  have hQle : P ^ (1 / 2 : ℝ) ≤ P * R := by
    have e : P ^ (1 : ℝ) * P ^ (-(1 / 8) : ℝ) = P ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add hP0]; norm_num
    rw [Real.rpow_one] at e
    rw [hRdef, e]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
  have hterm : ∀ d ∈ S,
      (d : ℝ) / (Nat.totient d : ℝ) / P * (d : ℝ) ^ (-(1 / 2) : ℝ) ≤
        K / P * (R + if (d : ℝ) ≤ P ^ (1 / 2 : ℝ) then 1 else 0) := by
    intro d hd
    obtain ⟨hd1, hdP⟩ := (hSmem d).mp hd
    have hdpos : 0 < d := hd1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hq : (d : ℝ) ^ (-(1 / 4) : ℝ) ≤
        R + if (d : ℝ) ≤ P ^ (1 / 2 : ℝ) then 1 else 0 := by
      by_cases hc : (d : ℝ) ≤ P ^ (1 / 2 : ℝ)
      · simp only [hc, ↓reduceIte]
        have hle := Real.rpow_le_one_of_one_le_of_nonpos hd1R
          (show (-(1 / 4) : ℝ) ≤ 0 by norm_num)
        linarith
      · simp only [hc, ↓reduceIte, add_zero]
        rw [← hQR]
        exact (Real.rpow_le_rpow_iff_of_neg hdR hQ0 (by norm_num)).mpr (le_of_not_ge hc)
    have e : (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-(3 / 4) : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) =
        (d : ℝ) ^ (-(1 / 4) : ℝ) := by
      rw [← Real.rpow_add hdR, ← Real.rpow_add hdR]; norm_num
    rw [Real.rpow_one] at e
    have hdm : 0 ≤ (d : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hdR.le _
    calc (d : ℝ) / (Nat.totient d : ℝ) / P * (d : ℝ) ^ (-(1 / 2) : ℝ)
        = (1 / (Nat.totient d : ℝ)) * ((d : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) / P) := by ring
      _ ≤ (K * (d : ℝ) ^ (-(3 / 4) : ℝ)) * ((d : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) / P) :=
          mul_le_mul_of_nonneg_right (hKb d hdpos) (by positivity)
      _ = K / P * ((d : ℝ) * (d : ℝ) ^ (-(3 / 4) : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ)) := by ring
      _ = K / P * (d : ℝ) ^ (-(1 / 4) : ℝ) := by rw [e]
      _ ≤ K / P * (R + if (d : ℝ) ≤ P ^ (1 / 2 : ℝ) then 1 else 0) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
  have hcardS : (S.card : ℝ) ≤ P := by
    rw [hSdef, Nat.card_Icc, Nat.add_sub_cancel]; exact Nat.floor_le hP0.le
  have hcardF : ((S.filter (fun d : ℕ => (d : ℝ) ≤ P ^ (1 / 2 : ℝ))).card : ℝ) ≤
      P ^ (1 / 2 : ℝ) := by
    have hsub : S.filter (fun d : ℕ => (d : ℝ) ≤ P ^ (1 / 2 : ℝ)) ⊆
        Finset.Icc 1 ⌊P ^ (1 / 2 : ℝ)⌋₊ := by
      intro d hd
      rw [Finset.mem_filter, hSmem] at hd
      rw [Finset.mem_Icc, Nat.le_floor_iff hQ0.le]
      exact ⟨hd.1.1, hd.2⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
    calc ((S.filter (fun d : ℕ => (d : ℝ) ≤ P ^ (1 / 2 : ℝ))).card : ℝ)
        ≤ ((⌊P ^ (1 / 2 : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ P ^ (1 / 2 : ℝ) := Nat.floor_le hQ0.le
  calc ∑ d ∈ S, (d : ℝ) / (Nat.totient d : ℝ) / P * (d : ℝ) ^ (-(1 / 2) : ℝ)
      ≤ ∑ d ∈ S, K / P * (R + if (d : ℝ) ≤ P ^ (1 / 2 : ℝ) then 1 else 0) :=
        Finset.sum_le_sum hterm
    _ = K / P * ((S.card : ℝ) * R +
          ((S.filter (fun d : ℕ => (d : ℝ) ≤ P ^ (1 / 2 : ℝ))).card : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_boole]
    _ ≤ K / P * (P * R + P * R) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (mul_le_mul_of_nonneg_right hcardS hR0.le) (hcardF.trans hQle)
    _ = 2 * K * R := by field_simp; ring

/-- P0069 page 8 display 2.8, raw form: for every `0 < h ≤ 1` and every `A > 0`, with
`D₀ = 2A + 14`, for `D ≥ D₀` and `x` large,
`Σ_{N ∈ [x, x + x^h], N even} (Σ_{d | N, d ≤ ℒ^{2D}} d/(φ(d) ℒ^{2D}))² ≤ C x^h ℒ^{-A-7}`.
The proof extends the divisor sum to all `d ≤ ℒ^{2D}`, see the file header. -/
theorem small_divisor_moment_raw512 (h : ℝ) (h0 : 0 < h) (h1 : h ≤ 1) :
    ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ h⌋₊).filter (fun N => Even N),
        (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Real.log x ^ (2 * D)),
          (d : ℝ) / (Nat.totient d : ℝ) / Real.log x ^ (2 * D)) ^ 2 ≤ C * x ^ h * Real.log x ^ (-A - 7) := by
  intro A hA
  have _hunused := h1
  obtain ⟨K, hK, hKb⟩ := one_div_totient_le512
  refine ⟨2 * A + 14, fun D hD => ?_⟩
  have hD0 : 0 ≤ 2 * D := by linarith
  have hlit := (isLittleO_log_rpow_rpow_atTop (2 * D) h0).bound
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hlit
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = 8 * K ^ 2 := ⟨_, rfl⟩
  refine ⟨max (max X0 (Real.exp 1)) C0, fun x hx => ?_⟩
  have hxX0 : X0 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxe : Real.exp 1 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hL0 : 0 < Real.log x := by linarith
  have hPH : Real.log x ^ (2 * D) ≤ x ^ h := by
    have hb := hX0 x hxX0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hb
    exact hb
  have hLApos : 0 < Real.log x ^ (-A - 7) := Real.rpow_pos_of_pos hL0 _
  have hH1 : 1 ≤ x ^ h := Real.one_le_rpow hx1 h0.le
  have hP1 : 1 ≤ Real.log x ^ (2 * D) := Real.one_le_rpow hL1 hD0
  have e1 : ((Real.log x ^ (2 * D)) ^ (-(1 / 8) : ℝ)) ^ 2 ≤ Real.log x ^ (-A - 7) := by
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast; linarith
  -- from here on the three quantities are opaque
  generalize hLdef : Real.log x = L at *
  generalize hHdef : x ^ h = H at *
  generalize hPdef : L ^ (2 * D) = P at *
  have hP0 : 0 < P := by linarith
  have hH0 : 0 < H := by linarith
  have hf0 : ∀ d : ℕ, (0 : ℝ) ≤ (d : ℝ) / (Nat.totient d : ℝ) / P := fun d => by positivity
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S = Finset.Icc 1 ⌊P⌋₊ := ⟨_, rfl⟩
  have hSmem : ∀ d : ℕ, d ∈ S ↔ 1 ≤ d ∧ (d : ℝ) ≤ P := by
    intro d
    rw [hSdef, Finset.mem_Icc, Nat.le_floor_iff hP0.le]
  -- pointwise: the divisors of N up to P lie in S
  have hpt : ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
      (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P),
        (d : ℝ) / (Nat.totient d : ℝ) / P) ^ 2 ≤
      (∑ d ∈ S, if d ∣ N then (d : ℝ) / (Nat.totient d : ℝ) / P else 0) ^ 2 := by
    intro N hN
    rw [Finset.mem_Icc] at hN
    have hxN : x ≤ (N : ℝ) := Nat.ceil_le.mp hN.1
    have hNR : (0 : ℝ) < (N : ℝ) := by linarith
    have hNpos : 0 < N := by exact_mod_cast hNR
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ => hf0 d))
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdN, _⟩, hdP⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN hNpos
      rw [Finset.mem_filter, hSmem]
      exact ⟨⟨hdpos, hdP⟩, hdN⟩
    · intro d _ _; exact hf0 d
  -- swap the order of summation and count multiples
  have hsmall := small_part512 x H hx0.le hH1 S
    (fun d => (d : ℝ) / (Nat.totient d : ℝ) / P) hf0
    (fun d hd => ⟨((hSmem d).mp hd).1, (((hSmem d).mp hd).2).trans hPH⟩)
  beta_reduce at hsmall
  have hinner : ∑ d ∈ S, (d : ℝ) / (Nat.totient d : ℝ) / P * (d : ℝ) ^ (-(1 / 2) : ℝ) ≤
      2 * K * P ^ (-(1 / 8) : ℝ) := by
    rw [hSdef]; exact small_weight_sum_le512 K hK hKb P hP1
  have hLm : 0 < L ^ (-A - 7) := hLApos
  have hmain : ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
      (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P),
        (d : ℝ) / (Nat.totient d : ℝ) / P) ^ 2 ≤ C0 * H * L ^ (-A - 7) := by
    calc ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
          (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P),
            (d : ℝ) / (Nat.totient d : ℝ) / P) ^ 2
        ≤ ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
          (∑ d ∈ S, if d ∣ N then (d : ℝ) / (Nat.totient d : ℝ) / P else 0) ^ 2 :=
          Finset.sum_le_sum hpt
      _ ≤ 2 * H * (∑ d ∈ S,
            (d : ℝ) / (Nat.totient d : ℝ) / P * (d : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 := hsmall
      _ ≤ 2 * H * (2 * K * P ^ (-(1 / 8) : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ =>
            mul_nonneg (hf0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))) hinner 2
      _ = 8 * K ^ 2 * H * (P ^ (-(1 / 8) : ℝ)) ^ 2 := by ring
      _ ≤ 8 * K ^ 2 * H * L ^ (-A - 7) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = C0 * H * L ^ (-A - 7) := by rw [hC0]
  calc ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => Even N),
        (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P),
          (d : ℝ) / (Nat.totient d : ℝ) / P) ^ 2
      ≤ ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
        (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P),
          (d : ℝ) / (Nat.totient d : ℝ) / P) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun N _ _ => sq_nonneg _)
    _ ≤ C0 * H * L ^ (-A - 7) := hmain
    _ ≤ max (max X0 (Real.exp 1)) C0 * H * L ^ (-A - 7) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hH0.le) hLm.le

end LeanLab.BHP1997.Route512
