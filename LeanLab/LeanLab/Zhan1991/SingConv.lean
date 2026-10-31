import LeanLab.Zhan1991.Statements

/-!
# The singular series products converge

Lab proof, unit U-5177. AI wrote this file. Known mathematics, no cited input.

VERIFY U-5175 noted that `Sing` and `SingPrinted` are `tprod`s with no convergence lemma, and that
an unconvergent `tprod` would be `1` by Mathlib's convention. Here both products are
`Multipliable`: each factor is `1 + a_p` with `|a_p| ≤ 1/(p-1)² ≤ 4/p²`, summable over primes.
So `Sing N` and `SingPrinted N` are the true infinite products of page 260.
-/

namespace LeanLab.Zhan1991

lemma summable_four_div_sq_primes :
    Summable fun p : {p : ℕ // p.Prime} ↦ (4 : ℝ) / ((p.1 : ℝ) ^ 2) := by
  have h : Summable fun n : ℕ ↦ (4 : ℝ) / ((n : ℝ) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 4
    simpa [div_eq_mul_inv] using this
  exact h.subtype {p | p.Prime}

lemma factor_bound {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : |a| ≤ 1 / ((p : ℝ) - 1) ^ 2) :
    ‖a‖ ≤ 4 / (p : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Real.norm_eq_abs]
  refine ha.trans ?_
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

lemma abs_cube_le {p : ℕ} (hp : p.Prime) :
    |1 / ((p : ℝ) - 1) ^ 3| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have h2 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hpos : 0 < (p : ℝ) - 1 := by linarith
  rw [abs_of_pos (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_le_pow_right₀ h2 (show 2 ≤ 3 by norm_num)]

/-- The corrected singular series converges. -/
theorem sing_multipliable (N : ℕ) : Multipliable fun p : {p : ℕ // p.Prime} ↦
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 + 1 / ((p.1 : ℝ) - 1) ^ 3 := by
  set a : {p : ℕ // p.Prime} → ℝ := fun p ↦
    if p.1 ∣ N then -(1 / ((p.1 : ℝ) - 1) ^ 2) else 1 / ((p.1 : ℝ) - 1) ^ 3 with ha
  have e : (fun p : {p : ℕ // p.Prime} ↦
      if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 + 1 / ((p.1 : ℝ) - 1) ^ 3) =
      fun p ↦ 1 + a p := by
    funext p; simp only [ha]; split_ifs <;> ring
  rw [e]
  refine Real.multipliable_one_add_of_summable ?_
  refine Summable.of_norm_bounded summable_four_div_sq_primes fun p ↦ ?_
  refine factor_bound p.2 ?_
  simp only [ha]
  split_ifs
  · rw [abs_neg, abs_of_nonneg (by positivity)]
  · exact abs_cube_le p.2

/-- The printed singular series converges too. -/
theorem singPrinted_multipliable (N : ℕ) : Multipliable fun p : {p : ℕ // p.Prime} ↦
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 - 1 / ((p.1 : ℝ) - 1) ^ 3 := by
  set a : {p : ℕ // p.Prime} → ℝ := fun p ↦
    if p.1 ∣ N then -(1 / ((p.1 : ℝ) - 1) ^ 2) else -(1 / ((p.1 : ℝ) - 1) ^ 3) with ha
  have e : (fun p : {p : ℕ // p.Prime} ↦
      if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 - 1 / ((p.1 : ℝ) - 1) ^ 3) =
      fun p ↦ 1 + a p := by
    funext p; simp only [ha]; split_ifs <;> ring
  rw [e]
  refine Real.multipliable_one_add_of_summable ?_
  refine Summable.of_norm_bounded summable_four_div_sq_primes fun p ↦ ?_
  refine factor_bound p.2 ?_
  simp only [ha]
  split_ifs
  · rw [abs_neg, abs_of_nonneg (by positivity)]
  · rw [abs_neg]; exact abs_cube_le p.2

/-- `∏_{n=2}^{M} (1 - 1/n²) = (M + 1)/(2M)`, so it is at least `1/2`. -/
lemma prod_Icc_one_sub_inv_sq (M : ℕ) (hM : 1 ≤ M) :
    ∏ n ∈ Finset.Icc 2 M, (1 - 1 / ((n : ℝ) ^ 2)) = ((M : ℝ) + 1) / (2 * M) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    push_cast
    field_simp
    ring

lemma prod_one_sub_inv_sq_ge (S : Finset ℕ) (hS : ∀ n ∈ S, 2 ≤ n) :
    1 / 2 ≤ ∏ n ∈ S, (1 - 1 / ((n : ℝ) ^ 2)) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · norm_num
  set M := S.max' hne
  have hM2 : 2 ≤ M := hS M (S.max'_mem hne)
  have hsub : S ⊆ Finset.Icc 2 M := fun n hn ↦
    Finset.mem_Icc.mpr ⟨hS n hn, S.le_max' n hn⟩
  have hfac : ∀ n ∈ Finset.Icc 2 M, 0 ≤ 1 - 1 / ((n : ℝ) ^ 2) ∧ 1 - 1 / ((n : ℝ) ^ 2) ≤ 1 := by
    intro n hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    constructor
    · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · have : 0 ≤ 1 / ((n : ℝ) ^ 2) := by positivity
      linarith
  have hle : ∏ n ∈ Finset.Icc 2 M, (1 - 1 / ((n : ℝ) ^ 2)) ≤
      ∏ n ∈ S, (1 - 1 / ((n : ℝ) ^ 2)) :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hsub (fun n hn ↦ (hfac n hn).1)
      (fun n hn _ ↦ (hfac n hn).2)
  rw [prod_Icc_one_sub_inv_sq M (by omega)] at hle
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have : (1 : ℝ) / 2 ≤ ((M : ℝ) + 1) / (2 * M) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  linarith

/-- For odd `N`, every finite partial product of `Sing N` over a set containing `2` is at
least `1`. -/
lemma partial_ge_one {N : ℕ} (hN : Odd N) (F : Finset {p : ℕ // p.Prime})
    (h2 : (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ F) :
    1 ≤ ∏ p ∈ F, (if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else
      1 + 1 / ((p.1 : ℝ) - 1) ^ 3) := by
  classical
  set two : {p : ℕ // p.Prime} := ⟨2, Nat.prime_two⟩
  set f : {p : ℕ // p.Prime} → ℝ := fun p ↦
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 + 1 / ((p.1 : ℝ) - 1) ^ 3
  set g : {p : ℕ // p.Prime} → ℝ := fun p ↦ 1 - 1 / ((p.1 : ℝ) - 1) ^ 2
  have hf2 : f two = 2 := by
    have : ¬ (2 ∣ N) := by
      rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hN
    simp only [f, two, this, ite_false]; norm_num
  have hodd : ∀ p ∈ F.erase two, 3 ≤ p.1 := by
    intro p hp
    have hne : p ≠ two := (Finset.mem_erase.mp hp).1
    have h2le := p.2.two_le
    by_contra hc
    have : p.1 = 2 := by omega
    exact hne (Subtype.ext this)
  have hfg : ∀ p ∈ F.erase two, 0 ≤ g p ∧ g p ≤ f p := by
    intro p hp
    have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast hodd p hp
    have hp1 : (2 : ℝ) ≤ (p.1 : ℝ) - 1 := by linarith
    have hg0 : 0 ≤ g p := by
      simp only [g]; rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    refine ⟨hg0, ?_⟩
    simp only [f, g]
    split_ifs
    · exact le_rfl
    · have : 0 ≤ 1 / ((p.1 : ℝ) - 1) ^ 3 := by positivity
      have : 0 ≤ 1 / ((p.1 : ℝ) - 1) ^ 2 := by positivity
      linarith
  have hprod : ∏ p ∈ F.erase two, g p ≤ ∏ p ∈ F.erase two, f p :=
    Finset.prod_le_prod₀ (fun p hp ↦ (hfg p hp).1) (fun p hp ↦ (hfg p hp).2)
  have himg : ∏ p ∈ F.erase two, g p =
      ∏ n ∈ (F.erase two).image (fun p : {p : ℕ // p.Prime} ↦ (p.1 - 1 : ℕ)),
        (1 - 1 / ((n : ℝ) ^ 2)) := by
    rw [Finset.prod_image]
    · refine Finset.prod_congr rfl fun p hp ↦ ?_
      simp only [g]
      have : 1 ≤ p.1 := p.2.one_lt.le
      rw [Nat.cast_sub this, Nat.cast_one]
    · intro p hp q hq h
      have := hodd p hp; have := hodd q hq
      have h' : p.1 - 1 = q.1 - 1 := h
      exact Subtype.ext (by omega)
  have hhalf : 1 / 2 ≤ ∏ p ∈ F.erase two, g p := by
    rw [himg]
    refine prod_one_sub_inv_sq_ge _ fun n hn ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have := hodd p hp; omega
  rw [← Finset.mul_prod_erase F f h2, hf2]
  linarith

/-- `𝔖(N) ≥ 1` for odd `N`. -/
theorem sing_ge_one {N : ℕ} (hN : Odd N) : 1 ≤ Sing N := by
  classical
  have hm := (sing_multipliable N).hasProd
  unfold Sing
  refine ge_of_tendsto hm ?_
  filter_upwards [Filter.eventually_ge_atTop {(⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime})}]
    with F hF
  exact partial_ge_one hN F (hF (Finset.mem_singleton_self _))

/-- The cited hypothesis `SingGtHalf` holds. -/
theorem singGtHalf : SingGtHalf := fun N hN ↦ lt_of_lt_of_le (by norm_num) (sing_ge_one hN)

/-- Theorem 1 gives solvability with `SingGtHalf` discharged. -/
theorem solvable_of_theorem1' (h1 : Theorem1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      Solvable N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) :=
  solvable_of_theorem1 h1 singGtHalf

end LeanLab.Zhan1991
