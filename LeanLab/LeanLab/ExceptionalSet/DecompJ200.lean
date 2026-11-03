import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998
import LeanLab.ExceptionalSet.State1539

/-!
Decomposition of Theorem 1 of P0082, Brüdern and Perelli 1998, repaired in unit U-1610.
Source: journal pages 357 display (6), 365 Lemma 8, 366 end of section 5.
The old leaves `leaf_dyadic_split`, `leaf_dyadic_sum` and `leaf_dyadic_sum_exp` were false and
`leaf_minor_bound`, `leaf_major_bound` were proved of two definitions equal to `0`; the old
`leaf_dyadic_bound` was Theorem 1 itself in dyadic form, so the old assembly was circular with the
sorry `BrudernPerelli1998.brudernPerelli`. Refutations are in `Audit1610`.
`leaf_dyadic_bound` is now an assembly from the major arc leaf, the minor arc leaf, the Fourier
identity leaf and the dissection leaf. Nothing here uses `brudernPerelli`.
-/

namespace LeanLab.ExceptionalSet.DecompJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998
open LeanLab.ExceptionalSet.U1539 (Sp majorArcs Kfun nu calE eC)

attribute [local instance] Classical.propDecidable

/-- Number of exceptions in the dyadic block `[M, 2M)`. Half open, so that the blocks at
`M = 2 ^ j` partition the positive integers, `n = 1` included. -/
noncomputable def Eγ_dyadic (γ : ℝ) (M : ℕ) : ℕ :=
  ((Finset.Ico M (2 * M)).filter (fun n => ¬ Solvable γ n)).card

/-- The dyadic indices `2 ^ j ≤ N`, `j ≤ log₂ N`. -/
noncomputable def dyadicIdx (N : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 N + 1)).image (fun j => 2 ^ j)

/-- The window of section 5, p. 366: `n ≤ 2N` with `X/2 < ν_n ≤ X`, `X = F(N)`. -/
noncomputable def window (γ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)

/-- The integral over the major arcs `𝔑` in (6) at `v = F(n)`, with `X = F(N)`, `P = X^{6δ}`,
`Δ = ℰ^{-1/8}`, `ℰ = exp(κ (log N)^{3-2γ})`, pp. 357 and 365. -/
noncomputable def majorInt (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
      * eC (-(α * F γ n))

/-- The integral over the minor arcs `𝔫 = ℝ \ 𝔑` in (6), same parameters. -/
noncomputable def minorInt (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ,
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
      * eC (-(α * F γ n))

/-- The `n` of the window where the major arc integral misses `c₀ X ℰ^{-1/10}`, Lemma 8 p. 365. -/
noncomputable def Eγ_major_block (γ δ κ c₀ : ℝ) (N : ℕ) : ℕ :=
  ((window γ N).filter (fun n =>
    (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card

/-- The `n` of the window where the minor arc integral exceeds `X ℰ^{-1/3}`, p. 366. -/
noncomputable def Eγ_minor_block (γ δ κ : ℝ) (N : ℕ) : ℕ :=
  ((window γ N).filter (fun n =>
    F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖)).card

/-- The members of a set `Bad` of integers lying in the window of `N`. -/
noncomputable def blockCount (γ : ℝ) (Bad : ℕ → Prop) (N : ℕ) : ℕ :=
  ((window γ N).filter Bad).card

/-- The members of a set `Bad` of integers lying in the block `[M, 2M)`. -/
noncomputable def dyadicCount (Bad : ℕ → Prop) (M : ℕ) : ℕ :=
  ((Finset.Ico M (2 * M)).filter Bad).card

/-- LEAF page 354: Trivial bound on dyadic exceptions. -/
theorem leaf_dyadic_trivial (γ : ℝ) (M : ℕ) :
    Eγ_dyadic γ M ≤ M := by
  unfold Eγ_dyadic
  have h : (Finset.Ico M (2 * M)).card = M := by
    rw [Nat.card_Ico]
    omega
  calc (Finset.Ico M (2 * M)).filter (fun n => ¬ Solvable γ n) |>.card
    _ ≤ (Finset.Ico M (2 * M)).card := Finset.card_filter_le _ _
    _ = M := h

/-- LEAF page 357, display (6). For large `N` every `n` of the window with no solution is bad for
the major arcs or for the minor arcs: `majorInt + minorInt = r(F(n))`, the sum (5) of
`log p₁ log p₂ w(p₁ + p₂ - F(n))` over `P < p₁, p₂ ≤ X`, and `w` vanishes off `|x| < 1`, so
`r(F(n)) = 0` when `n` has no solution. Then `(majorInt).re ≤ ‖minorInt‖`, and
`ℰ^{-1/3} < c₀ ℰ^{-1/10}` for large `N`. -/
theorem leaf_dyadic_split (γ δ κ c₀ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ) (hκ : 0 < κ)
    (hc₀ : 0 < c₀) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      blockCount γ (fun n => ¬ Solvable γ n) N ≤
        Eγ_minor_block γ δ κ N + Eγ_major_block γ δ κ c₀ N := by sorry

/-- LEAF page 366, the variance bound of section 5, from Theorem 2 with `c = 1 - 3δ`, Vinogradov's
bound for `S` on `𝔫` and Chebyshev. The paper states the exceptions as `O(N ℰ^{-1/4})`; we ask only
for the weaker `O(N ℰ^{-1/12})`, which is all that the proof of Theorem 1 uses. -/
theorem leaf_minor_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_minor_block γ δ κ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by sorry

/-- LEAF page 365, Lemma 8, with one `κ` shared by the two arcs as in the paper, where `ℰ` is
fixed once for sections 4 to 7. `U1539.Lemma8` is the same bound with a private `κ`, too weak to
combine with `leaf_minor_bound`. -/
theorem leaf_major_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by sorry

/-- ASSEMBLY of the three leaves above, p. 366: `r(F(n)) > 0` for all but `O(N ℰ^{-1/12})` values
of `n` with `X/2 < ν_n ≤ X`. -/
theorem block_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
        B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₁, hδ₁, hmin⟩ := leaf_minor_bound γ h1 h2
  obtain ⟨δ₂, hδ₂, hmaj⟩ := leaf_major_bound γ h1 h2
  have hδ : 0 < min δ₁ δ₂ / 2 := half_pos (lt_min hδ₁ hδ₂)
  have hδ1 : min δ₁ δ₂ / 2 < δ₁ := by
    have := min_le_left δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  have hδ2 : min δ₁ δ₂ / 2 < δ₂ := by
    have := min_le_right δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  obtain ⟨κ₁, hκ₁, hmin⟩ := hmin _ hδ hδ1
  obtain ⟨κ₂, hκ₂, hmaj⟩ := hmaj _ hδ hδ2
  have hκ : 0 < min κ₁ κ₂ := lt_min hκ₁ hκ₂
  obtain ⟨B₁, hB₁, N₁, hmin⟩ := hmin _ hκ (min_le_left _ _)
  obtain ⟨c₀, B₂, hc₀, hB₂, N₂, hmaj⟩ := hmaj _ hκ (min_le_right _ _)
  obtain ⟨N₃, hsplit⟩ := leaf_dyadic_split γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ h1 h2 hδ hκ hc₀
  refine ⟨min κ₁ κ₂, B₁ + B₂, hκ, add_pos hB₁ hB₂, max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have h₁ := hmin N (le_trans (le_max_left _ _) hN)
  have h₂ := hmaj N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h₃ := hsplit N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have h₃' : (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
      Eγ_minor_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) N +
        Eγ_major_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ N := by exact_mod_cast h₃
  calc _ ≤ _ := h₃'
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring

/-- LEAF page 366, "a routine dyadic dissection argument", last line of section 5. For any set
`Bad`: a block bound in the windows of `F` gives a saving on `[M, 2M)`. The block `[M, 2M)` meets
about `log₂ (F(2M)/F(M)) ≪ (log M)^γ` windows, each of size at most `B N ℰ^{-1/12}`, and that power
of `log M` is absorbed by the exponential. -/
theorem leaf_block_dissection (γ κ B : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hB : 0 < B)
    (Bad : ℕ → Prop) (N₀ : ℕ)
    (h : ∀ N : ℕ, N₀ ≤ N → (blockCount γ Bad N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (dyadicCount Bad M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by sorry

/-- ASSEMBLY page 366 and 367. No longer Theorem 1 restated: it follows from `block_bound` and the
dissection leaf, and does not use `BrudernPerelli1998.brudernPerelli`. -/
theorem leaf_dyadic_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  obtain ⟨κ, B, hκ, hB, N₀, h⟩ := block_bound γ h1 h2
  obtain ⟨c, hc, C, hC, M0, hM⟩ :=
    leaf_block_dissection γ κ B h1 h2 hκ hB (fun n => ¬ Solvable γ n) N₀ h
  refine ⟨c, hc, C, hC, M0, fun M hM0 => ?_⟩
  have e : Eγ_dyadic γ M = dyadicCount (fun n => ¬ Solvable γ n) M := by
    unfold Eγ_dyadic dyadicCount
    congr!
  rw [e]
  exact hM M hM0

/-- PROVED. The total exceptions up to `N` are at most the sum over the dyadic blocks. -/
theorem leaf_dyadic_sum (γ : ℝ) (N : ℕ) :
    (Eγ γ N : ℝ) ≤ (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ)) := by
  have hsub : (Finset.Icc 1 N).filter (fun n => ¬ Solvable γ n) ⊆
      (dyadicIdx N).biUnion (fun i => (Finset.Ico i (2 * i)).filter (fun n => ¬ Solvable γ n)) := by
    intro n hn
    obtain ⟨hn, hb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    refine Finset.mem_biUnion.mpr ⟨2 ^ Nat.log 2 n, ?_, Finset.mem_filter.mpr ⟨?_, hb⟩⟩
    · refine Finset.mem_image.mpr ⟨Nat.log 2 n, ?_, rfl⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hnN))
    · refine Finset.mem_Ico.mpr ⟨Nat.pow_log_le_self 2 (by omega), ?_⟩
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      rw [pow_succ] at this
      omega
  have hcard : Eγ γ N ≤ ∑ i ∈ dyadicIdx N, Eγ_dyadic γ i :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  exact_mod_cast hcard

/-- For `0 < p ≤ 1` and `0 ≤ y`, `y ^ p ≤ y + 1`. -/
private lemma rpow_le_self_add_one {y p : ℝ} (hy : 0 ≤ y) (hp : 0 < p) (hp1 : p ≤ 1) :
    y ^ p ≤ y + 1 := by
  by_cases h : y ≤ 1
  · have := Real.rpow_le_one hy h hp.le
    linarith
  · have hy1 : (1 : ℝ) < y := not_le.mp h
    have h' := Real.rpow_le_rpow_of_exponent_le hy1.le hp1
    rw [Real.rpow_one] at h'
    linarith

/-- PROVED, page 367. The sum of the exponential bound over the dyadic blocks: the sum runs over
`M = 2 ^ j ≤ N` and is geometric; over all `M ≤ N` it would be about `N²` times the exponential. -/
theorem leaf_dyadic_sum_exp (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ dyadicIdx N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ)
      ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ)) := by
  set p : ℝ := 3 - 2 * γ with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  set d : ℝ := min c (1 / 2) with hd
  have hd0 : 0 < d := lt_min hc (by norm_num)
  have hdc : d ≤ c := min_le_left _ _
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  refine ⟨d, hd0, C * Real.exp d * 4, by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  set L : ℝ := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hN1
  set sN : ℝ := Real.exp (L / 2) with hsN
  have hsN0 : 0 < sN := Real.exp_pos _
  have hsN2 : sN ^ 2 = N := by
    rw [hsN, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (L / 2) = L := by push_cast; ring
    rw [this, hL, Real.exp_log hN0]
  set r : ℝ := Real.exp (Real.log 2 / 2) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ^ 2 = 2 := by
    rw [hr, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (Real.log 2 / 2) = Real.log 2 := by push_cast; ring
    rw [this, Real.exp_log (by norm_num)]
  have hr43 : 4 / 3 ≤ r := by
    by_contra hlt
    have hlt' : r < 4 / 3 := not_le.mp hlt
    nlinarith
  have hgeom : ∀ J : ℕ, ∑ j ∈ Finset.range (J + 1), r ^ j ≤ 4 * r ^ J := by
    intro J
    induction J with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ r n]
      have hrn : 0 < r ^ n := pow_pos hr0 n
      nlinarith
  have hterm : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      C * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c * Real.log ((2 ^ j : ℕ) : ℝ) ^ p) ≤
        (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * r ^ j := by
    intro j hj
    have hjN : 2 ^ j ≤ N := by
      have hj' : j ≤ Nat.log 2 N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (Nat.pow_le_pow_right (by norm_num) hj').trans (Nat.pow_log_le_self 2 (by omega))
    have hM1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    set x : ℝ := Real.log ((2 ^ j : ℕ) : ℝ) with hx
    have hx0 : 0 ≤ x := Real.log_nonneg hM1
    have hxL : x ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hjN)
    have hy0 : 0 ≤ L - x := by linarith
    have hsub : L ^ p ≤ x ^ p + (L - x) ^ p := by
      have := Real.rpow_add_le_add_rpow hx0 hy0 hp.le hp1.le
      rwa [add_sub_cancel] at this
    have hy1 : (L - x) ^ p ≤ (L - x) + 1 := rpow_le_self_add_one hy0 hp hp1.le
    have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx0 _
    have hyp : 0 ≤ (L - x) ^ p := Real.rpow_nonneg hy0 _
    have hkey : -c * x ^ p ≤ d + -d * L ^ p + (L - x) / 2 := by
      have e1 : d * L ^ p ≤ d * x ^ p + d * (L - x) ^ p := by nlinarith
      have e2 : d * x ^ p ≤ c * x ^ p := mul_le_mul_of_nonneg_right hdc hxp
      have e3 : d * (L - x) ^ p ≤ d * ((L - x) + 1) := mul_le_mul_of_nonneg_left hy1 hd0.le
      have e4 : d * (L - x) ≤ (1 / 2) * (L - x) := mul_le_mul_of_nonneg_right hd2 hy0
      nlinarith
    have hexp := Real.exp_le_exp.mpr hkey
    have hxval : ((2 ^ j : ℕ) : ℝ) = Real.exp x := by
      rw [hx, Real.exp_log (by linarith)]
    have hrj : r ^ j = Real.exp (x / 2) := by
      rw [hr, ← Real.exp_nat_mul, hx]
      congr 1
      push_cast
      rw [Real.log_pow]
      ring
    have hcomb : Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2) =
        Real.exp d * Real.exp (-d * L ^ p) * sN * Real.exp (x / 2) := by
      rw [hsN]
      simp only [← Real.exp_add]
      congr 1
      ring
    rw [hrj]
    calc C * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c * x ^ p)
        = C * Real.exp x * Real.exp (-c * x ^ p) := by rw [← hxval]
      _ ≤ C * Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * (Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2)) := by ring
      _ = _ := by rw [hcomb]; ring
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j)
      (Finset.range (Nat.log 2 N + 1) : Set ℕ) :=
    fun _ _ _ _ h => Nat.pow_right_injective (le_refl 2) h
  unfold dyadicIdx
  rw [Finset.sum_image hinj]
  have hA : 0 ≤ C * Real.exp d * Real.exp (-d * L ^ p) * sN := by positivity
  have hrJ : r ^ Nat.log 2 N ≤ sN := by
    have h2J : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have : (r ^ Nat.log 2 N) ^ 2 ≤ sN ^ 2 := by
      rw [hsN2, ← pow_mul, mul_comm, pow_mul, hr2]
      exact_mod_cast h2J
    exact (pow_le_pow_iff_left₀ (by positivity) hsN0.le (by norm_num)).mp this
  calc _ ≤ ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * r ^ j := Finset.sum_le_sum hterm
    _ = (C * Real.exp d * Real.exp (-d * L ^ p) * sN) *
        ∑ j ∈ Finset.range (Nat.log 2 N + 1), r ^ j := by rw [Finset.mul_sum]
    _ ≤ (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * (4 * sN) :=
        mul_le_mul_of_nonneg_left ((hgeom _).trans (by linarith)) hA
    _ = C * Real.exp d * 4 * sN ^ 2 * Real.exp (-d * L ^ p) := by ring
    _ = _ := by rw [hsN2]

/-- For `N ≥ 2` and `0 < p < 1`, the factor `N * exp (-c * (log N) ^ p)` dominates the constant
`exp (-c) * 2 ^ (1 - c)` when `0 < c ≤ 1`. -/
private lemma le_mul_exp_neg_mul_log_rpow {c p : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 0 < p) (hp1 : p < 1) {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (-c) * (2 : ℝ) ^ (1 - c) ≤
      (N : ℝ) * Real.exp (-c * Real.log N ^ p) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hstep : Real.log N ^ p ≤ Real.log N + 1 := rpow_le_self_add_one hlog hp hp1.le
  have hmul : c * Real.log N ^ p ≤ c * (Real.log N + 1) :=
    mul_le_mul_of_nonneg_left hstep hc.le
  have hexp_le : Real.exp (-c * Real.log N - c) ≤ Real.exp (-c * Real.log N ^ p) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : (0 : ℝ) ≤ 1 - c := by linarith
  have hNpow : (2 : ℝ) ^ (1 - c) ≤ (N : ℝ) ^ (1 - c) :=
    Real.rpow_le_rpow (by norm_num) hN2 hpow
  have hmain : (N : ℝ) * Real.exp (-c * Real.log N) = (N : ℝ) ^ (1 - c) := by
    calc (N : ℝ) * Real.exp (-c * Real.log N)
        = Real.exp (Real.log N) * Real.exp (-c * Real.log N) := by rw [Real.exp_log hNpos]
      _ = Real.exp (Real.log N + -c * Real.log N) := by rw [← Real.exp_add]
      _ = Real.exp (Real.log N * (1 - c)) := by
          congr 1
          ring
      _ = (N : ℝ) ^ (1 - c) := by rw [Real.rpow_def_of_pos hNpos]
  calc Real.exp (-c) * (2 : ℝ) ^ (1 - c)
      ≤ Real.exp (-c) * (N : ℝ) ^ (1 - c) :=
        mul_le_mul_of_nonneg_left hNpow (Real.exp_pos _).le
    _ = Real.exp (-c) * ((N : ℝ) * Real.exp (-c * Real.log N)) := by rw [hmain]
    _ = (N : ℝ) * (Real.exp (-c) * Real.exp (-c * Real.log N)) := by ring
    _ = (N : ℝ) * Real.exp (-c * Real.log N - c) := by
        congr 1
        rw [← Real.exp_add]
        ring
    _ ≤ (N : ℝ) * Real.exp (-c * Real.log N ^ p) :=
        mul_le_mul_of_nonneg_left hexp_le hNpos.le

/-- LEAF page 367: Given the exponential sum bound and dyadic sum bound, Theorem 1 holds. -/
theorem leaf_theorem1_from_sums (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    (∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ))) →
    (∀ M : ℕ, Eγ_dyadic γ M ≤ M) →
    (∀ N : ℕ, (Eγ γ N : ℝ) ≤ (∑ i ∈ dyadicIdx N, Eγ_dyadic γ i : ℝ)) →
    (∀ c C : ℝ, 0 < c → 0 < C → ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ dyadicIdx N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ) ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ))) →
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (Eγ γ N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
  intro hA hB hC hD
  obtain ⟨c₀, hc₀, C₀, hC₀, M₀, hM₀⟩ := hA
  obtain ⟨c₁, hc₁, C₁, hC₁, hD₁⟩ := hD c₀ C₀ hc₀ hC₀
  have hp : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  set c : ℝ := min c₁ (1 / 2) with hcdef
  have hc : 0 < c := by
    rw [hcdef]; exact lt_min hc₁ (by norm_num)
  have hcc₁ : c ≤ c₁ := by
    rw [hcdef]; exact min_le_left _ _
  have hc1 : c ≤ 1 := by
    rw [hcdef]; have := min_le_right c₁ (1 / 2 : ℝ); linarith
  have hδ : 0 < Real.exp (-c) * (2 : ℝ) ^ (1 - c) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨c, hc, (M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnonneg : (0 : ℝ) ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg hlogN _
  have hexp_le : Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) ≤
      Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsplit : (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ))
      = (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      + (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not (dyadicIdx N) (fun i => i < M₀)
      (fun i => (Eγ_dyadic γ i : ℝ))).symm
  have hpart1 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ (M₀ : ℝ) ^ 2 := by
    have h1 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact_mod_cast hB i
    have h2 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ)) ≤ (M₀ : ℝ) ^ 2 := by
      have hcard : ((dyadicIdx N).filter (fun i => i < M₀)).card ≤ M₀ := by
        have hsub : (dyadicIdx N).filter (fun i => i < M₀) ⊆ Finset.range M₀ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact hi.2
        calc _ ≤ (Finset.range M₀).card := Finset.card_le_card hsub
          _ = M₀ := Finset.card_range M₀
      have hcard' : (((dyadicIdx N).filter (fun i => i < M₀)).card : ℝ) ≤ (M₀ : ℝ) := by
        exact_mod_cast hcard
      have hM₀nn : (0 : ℝ) ≤ (M₀ : ℝ) := by positivity
      calc (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ))
          ≤ ∑ _i ∈ (dyadicIdx N).filter (fun i => i < M₀), (M₀ : ℝ) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hi' : i < M₀ := (Finset.mem_filter.mp hi).2
            exact_mod_cast hi'.le
        _ = (((dyadicIdx N).filter (fun i => i < M₀)).card : ℝ) * (M₀ : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (M₀ : ℝ) * (M₀ : ℝ) := by nlinarith
        _ = (M₀ : ℝ) ^ 2 := by ring
    linarith
  have hpart2 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by
    have hle1 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hiM : M₀ ≤ i := by
        have := (Finset.mem_filter.mp hi).2
        omega
      exact hM₀ i hiM
    have hle2 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))))
        ≤ ∑ i ∈ dyadicIdx N, (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro i _ _
      positivity
    linarith [hD₁ N hN]
  have hDbound : (M₀ : ℝ) ^ 2 ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
      * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by
    have hkey := le_mul_exp_neg_mul_log_rpow (c := c) (p := 3 - 2 * γ) hc hc1 hp hp1 hN
    calc (M₀ : ℝ) ^ 2
        = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) := by field_simp
      _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) :=
          mul_le_mul_of_nonneg_left hkey (div_nonneg (sq_nonneg _) hδ.le)
  have hC₁le : C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
      ≤ C₁ * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    have h1 : (0 : ℝ) ≤ C₁ * (N : ℝ) := by positivity
    calc C₁ * (N : ℝ) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
        = (C₁ * (N : ℝ)) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by ring
      _ ≤ (C₁ * (N : ℝ)) * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) :=
          mul_le_mul_of_nonneg_left hexp_le h1
  calc (Eγ γ N : ℝ)
      ≤ (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ)) := hC N
    _ = (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        + (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) := hsplit
    _ ≤ (M₀ : ℝ) ^ 2 + C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by linarith
    _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁)
        * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by nlinarith
    _ = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁) * N
        * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by ring

/-- ASSEMBLY. Theorem 1 of Brudern and Perelli 1998 from leaves. -/
theorem brudernPerelli_assembly : Theorem1 := by
  intro γ h1 h2
  exact leaf_theorem1_from_sums γ h1 h2
    (leaf_dyadic_bound γ h1 h2)
    (leaf_dyadic_trivial γ)
    (leaf_dyadic_sum γ)
    (leaf_dyadic_sum_exp γ h1 h2)

end LeanLab.ExceptionalSet.DecompJ200
