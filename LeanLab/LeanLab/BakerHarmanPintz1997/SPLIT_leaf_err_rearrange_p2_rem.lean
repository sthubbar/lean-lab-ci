/-
Proved pieces for `leaf_err_remainder` of SPLIT_leaf_err_rearrange, display (4.13) of P0069,
page 27: the + 2 terms of the interval count total at most C x^0.96.
The pieces follow the paper's estimate: the number of m and n is at most (M + 1)(N + 1),
the number of d is at most gamma w + 1, each coefficient is at most tau^B, which is x^o(1)
by the divisor bound, and w = exp(L^(9/10)) is x^o(1).
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_Decomp409b
import LeanLab.HeathBrown1985.DivisorEps

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-- Proved glue: tau m to a real power B is at most the number of divisors of m to the
natural power ceiling of B, as tau m is at least 1 for m at least 1. -/
theorem tau_rpow_le_card_pow (B : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    tau m ^ B ≤ (m.divisors.card : ℝ) ^ (⌈B⌉₊) := by
  have ht : tau m = (m.divisors.card : ℝ) := by
    simp [tau, ArithmeticFunction.sigma_zero_apply]
  have h1 : (1 : ℝ) ≤ tau m := by
    rw [ht]
    exact_mod_cast Finset.card_pos.2 (Nat.nonempty_divisors.2 (by omega))
  rw [← ht, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil B)

/-- Proved glue: under (4.8) or (4.9) with ε below 1, M and N are at most x for x at least 1. -/
theorem MN_le_self_of_size {ε x M N : ℝ} (hx : 1 ≤ x) (hε : ε < 1)
    (h : max (x ^ (0.45 : ℝ)) M * max (x ^ (0.225 : ℝ)) N ≤ x ^ (0.775 : ℝ) ∨
      max M N ≤ x ^ (0.46 + ε / 8)) : M ≤ x ∧ N ≤ x := by
  have hx0 : 0 < x := by linarith
  rcases h with h | h
  · have h225 : 0 < x ^ (0.225 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have h45 : 0 < x ^ (0.45 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hmax1 : 0 < max (x ^ (0.45 : ℝ)) M := lt_of_lt_of_le h45 (le_max_left _ _)
    constructor
    · by_cases hM0 : M ≤ 0
      · linarith
      push_neg at hM0
      have hMx : M * x ^ (0.225 : ℝ) ≤ x ^ (0.55 : ℝ) * x ^ (0.225 : ℝ) := by
        calc M * x ^ (0.225 : ℝ) ≤ max (x ^ (0.45 : ℝ)) M * max (x ^ (0.225 : ℝ)) N :=
              mul_le_mul (le_max_right _ _) (le_max_left _ _) h225.le hmax1.le
          _ ≤ x ^ (0.775 : ℝ) := h
          _ = x ^ (0.55 : ℝ) * x ^ (0.225 : ℝ) := by
              rw [← Real.rpow_add hx0]; norm_num
      have := le_of_mul_le_mul_right hMx h225
      have h1 : x ^ (0.55 : ℝ) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      rw [Real.rpow_one] at h1
      linarith
    · by_cases hN0 : N ≤ 0
      · linarith
      push_neg at hN0
      have hNx : x ^ (0.45 : ℝ) * N ≤ x ^ (0.45 : ℝ) * x ^ (0.325 : ℝ) := by
        calc x ^ (0.45 : ℝ) * N ≤ max (x ^ (0.45 : ℝ)) M * max (x ^ (0.225 : ℝ)) N :=
              mul_le_mul (le_max_left _ _) (le_max_right _ _) hN0.le hmax1.le
          _ ≤ x ^ (0.775 : ℝ) := h
          _ = x ^ (0.45 : ℝ) * x ^ (0.325 : ℝ) := by
              rw [← Real.rpow_add hx0]; norm_num
      have := le_of_mul_le_mul_left hNx h45
      have h1 : x ^ (0.325 : ℝ) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      rw [Real.rpow_one] at h1
      linarith
  · have h1 : x ^ (0.46 + ε / 8) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    rw [Real.rpow_one] at h1
    exact ⟨le_trans (le_max_left _ _) (h.trans h1), le_trans (le_max_right _ _) (h.trans h1)⟩

/-- Proved piece, display (4.13) remainder: by the divisor bound, tau(m)^B is at most
Ca x^(1/1000) for 1 at most m at most 2x, from the lab's PROVED
`HeathBrown1985.card_divisors_le_rpow`. -/
theorem rem_coef_le (B : ℝ) : ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ x : ℝ, 1 ≤ x → ∀ m : ℕ, 1 ≤ m →
    (m : ℝ) ≤ 2 * x → tau m ^ B ≤ Ca * x ^ (1 / 1000 : ℝ) := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = ⌈B⌉₊ := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = 1000 * (r + 1) := ⟨_, rfl⟩
  have hk : 1 ≤ k := by omega
  obtain ⟨Cd, hCd, hd⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨Cd ^ r * 2, by positivity, fun x hx m hm hmx => ?_⟩
  have hk' : (k : ℝ) = 1000 * ((r : ℝ) + 1) := by rw [hkdef]; push_cast; ring
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (k : ℝ)⁻¹ * r := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he1 : e ≤ 1 / 1000 := by
    rw [he, hk', ← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hpow : ((m : ℝ) ^ ((k : ℝ)⁻¹)) ^ r = (m : ℝ) ^ e := by
    rw [he, Real.rpow_mul_natCast hm0]
  calc tau m ^ B ≤ (m.divisors.card : ℝ) ^ r := hr ▸ tau_rpow_le_card_pow B hm
    _ ≤ (Cd * (m : ℝ) ^ ((k : ℝ)⁻¹)) ^ r :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hd m hm) r
    _ = Cd ^ r * (m : ℝ) ^ e := by rw [mul_pow, hpow]
    _ ≤ Cd ^ r * (2 * x) ^ e :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm0 hmx he0) (by positivity)
    _ = Cd ^ r * (2 ^ e * x ^ e) := by rw [Real.mul_rpow (by norm_num) (by linarith)]
    _ ≤ Cd ^ r * (2 * x ^ (1 / 1000 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2 : (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [Real.rpow_one] at h2
        have h3 : x ^ e ≤ x ^ (1 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx he1
        have h4 : 0 ≤ x ^ e := Real.rpow_nonneg (by linarith) _
        nlinarith
    _ = Cd ^ r * 2 * x ^ (1 / 1000 : ℝ) := by ring

/-- Proved piece, display (4.13) remainder: w = exp(L^(9/10)) is at most x^(1/1000) once
L x is at least 10^30. -/
theorem rem_wof_le {x : ℝ} (hx : Real.exp (10 ^ 30) ≤ x) : wof x ≤ x ^ (1 / 1000 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have ht : (10 : ℝ) ^ 30 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  set t := Real.log x with htdef
  have ht0 : 0 < t := by linarith
  have h1000 : (1000 : ℝ) ≤ t ^ (((10 : ℕ) : ℝ)⁻¹) := by
    have e : (1000 : ℝ) = ((1000 : ℝ) ^ (10 : ℕ)) ^ (((10 : ℕ) : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
    rw [e]
    exact Real.rpow_le_rpow (by positivity) (by norm_num at ht ⊢; linarith) (by positivity)
  have hsplit : t ^ (9 / 10 : ℝ) * t ^ (((10 : ℕ) : ℝ)⁻¹) = t := by
    rw [← Real.rpow_add ht0]; norm_num
  have h9 : 0 ≤ t ^ (9 / 10 : ℝ) := Real.rpow_nonneg ht0.le _
  unfold wof
  rw [Real.rpow_def_of_pos hx0, ← htdef]
  apply Real.exp_le_exp.2
  nlinarith

/-- Proved piece, display (4.13) remainder: the d with d | P(w) and gamma at most d below
gamma w number at most gamma w + 1. -/
theorem rem_card_D_le (γ w : ℝ) (hγw : 0 ≤ γ * w) :
    (((siftingProduct w).divisors.filter
      (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) ≤ γ * w + 1 := by
  have hsub : (siftingProduct w).divisors.filter (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w) ⊆
      (Finset.range ⌈γ * w⌉₊).image (fun n : ℕ => (n : ℝ)) := by
    intro i hi
    simp at hi
    obtain ⟨⟨a, _, rfl⟩, _, h3⟩ := hi
    rw [Finset.mem_image]
    exact ⟨a, Finset.mem_range.2 (Nat.lt_ceil.2 h3), rfl⟩
  calc _ ≤ (((Finset.range ⌈γ * w⌉₊).image (fun n : ℕ => (n : ℝ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Finset.range ⌈γ * w⌉₊).card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ = (⌈γ * w⌉₊ : ℝ) := by rw [Finset.card_range]
    _ ≤ γ * w + 1 := (Nat.ceil_lt_add_one hγw).le

/-- Proved piece, display (4.13) remainder: the dyadic block (M, 2M] holds at most
max 1 M + 1 integers. -/
theorem rem_card_Ioc_le (M : ℝ) :
    ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) ≤ max 1 M + 1 := by
  rw [Nat.card_Ioc]
  by_cases hM : M ≤ 0
  · rw [Nat.floor_of_nonpos (by linarith : 2 * M ≤ 0)]
    simp only [Nat.zero_sub, Nat.cast_zero]
    have := le_max_left (1 : ℝ) M
    linarith
  push_neg at hM
  have hle : ⌊M⌋₊ ≤ ⌊2 * M⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub hle]
  have h1 : (⌊2 * M⌋₊ : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
  have h2 : M - 1 < (⌊M⌋₊ : ℝ) := Nat.sub_one_lt_floor M
  have := le_max_right (1 : ℝ) M
  linarith

/-- Proved piece, display (4.13) remainder: under (4.8) or (4.9), for x at least 1 and
ε at least 0, (max 1 M + 1)(max 1 N + 1) is at most 4 x^(0.92 + ε/4). -/
theorem rem_size_le {ε x M N : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (h : max (x ^ (0.45 : ℝ)) M * max (x ^ (0.225 : ℝ)) N ≤ x ^ (0.775 : ℝ) ∨
      max M N ≤ x ^ (0.46 + ε / 8)) :
    (max 1 M + 1) * (max 1 N + 1) ≤ 4 * x ^ (0.92 + ε / 4) := by
  have hx0 : 0 < x := by linarith
  rcases h with h | h
  · have h45 : 1 ≤ x ^ (0.45 : ℝ) := Real.one_le_rpow hx (by norm_num)
    have h225 : 1 ≤ x ^ (0.225 : ℝ) := Real.one_le_rpow hx (by norm_num)
    have hA : max 1 M + 1 ≤ 2 * max (x ^ (0.45 : ℝ)) M := by
      have := le_max_left (x ^ (0.45 : ℝ)) M
      have := le_max_right (x ^ (0.45 : ℝ)) M
      rcases le_total 1 M with h1 | h1
      · rw [max_eq_right h1]; linarith
      · rw [max_eq_left h1]; linarith
    have hB : max 1 N + 1 ≤ 2 * max (x ^ (0.225 : ℝ)) N := by
      have := le_max_left (x ^ (0.225 : ℝ)) N
      have := le_max_right (x ^ (0.225 : ℝ)) N
      rcases le_total 1 N with h1 | h1
      · rw [max_eq_right h1]; linarith
      · rw [max_eq_left h1]; linarith
    have hexp : x ^ (0.775 : ℝ) ≤ x ^ (0.92 + ε / 4) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hA0 : 0 ≤ max 1 M + 1 := by have := le_max_left (1 : ℝ) M; linarith
    have hB0 : 0 ≤ max 1 N + 1 := by have := le_max_left (1 : ℝ) N; linarith
    calc (max 1 M + 1) * (max 1 N + 1)
        ≤ (2 * max (x ^ (0.45 : ℝ)) M) * (2 * max (x ^ (0.225 : ℝ)) N) :=
          mul_le_mul hA hB hB0 (le_trans hA0 hA)
      _ = 4 * (max (x ^ (0.45 : ℝ)) M * max (x ^ (0.225 : ℝ)) N) := by ring
      _ ≤ 4 * x ^ (0.92 + ε / 4) := by linarith
  · have hP : 1 ≤ x ^ (0.46 + ε / 8) := Real.one_le_rpow hx (by linarith)
    have hM : max 1 M ≤ x ^ (0.46 + ε / 8) :=
      max_le hP (le_trans (le_max_left _ _) h)
    have hN : max 1 N ≤ x ^ (0.46 + ε / 8) :=
      max_le hP (le_trans (le_max_right _ _) h)
    have hA0 : 0 ≤ max 1 M + 1 := by have := le_max_left (1 : ℝ) M; linarith
    have hB0 : 0 ≤ max 1 N + 1 := by have := le_max_left (1 : ℝ) N; linarith
    have hsq : x ^ (0.46 + ε / 8) * x ^ (0.46 + ε / 8) = x ^ (0.92 + ε / 4) := by
      rw [← Real.rpow_add hx0]; ring_nf
    calc (max 1 M + 1) * (max 1 N + 1)
        ≤ (2 * x ^ (0.46 + ε / 8)) * (2 * x ^ (0.46 + ε / 8)) :=
          mul_le_mul (by linarith) (by linarith) hB0 (by linarith)
      _ = 4 * (x ^ (0.46 + ε / 8) * x ^ (0.46 + ε / 8)) := by ring
      _ = 4 * x ^ (0.92 + ε / 4) := by rw [hsq]

end LeanLab.BakerHarmanPintz1997.Decomp409b
