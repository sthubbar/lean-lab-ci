/-
Unit U-1537, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0035, J. Pintz and I. Z. Ruzsa 2020, On Linnik's approximation to Goldbach's problem II,
Acta Math. Hungar. Read from the PC copy copies/P0035.pdf, page numbers as printed; page images
of pp. 4 to 6 checked.

File b: the steps of Section 2, pp. 3 to 6, by which part II turns the explicit formula of
[Pin2], its Theorem 2 on p. 4, into Corollary 1 on p. 5, and the zero inputs (2.28) to (2.31)
on pp. 5 and 6 into the growth of the exceptional moduli, (2.27) and (2.32).

The explicit formula itself, Jutila's density bound (2.15), the real zero bound of [Pin1] or
[GS] behind (2.29) and Iwaniec's zero free region (2.30) are external theorems; they are NOT
entered as sorries here. They appear as hypotheses of the assemblies, in the exact shape the
paper uses them, so each assembly says precisely what it takes from them.

* `I1`, `Irho`: `I(h)` and `I(h, ϱ_i, ϱ_j)` of (2.16), (2.17) p. 4.
* Assembly `cor1_of_thm2`: (2.25) of Corollary 1 from the shape (2.19) of Theorem 2, the choice
  (2.22), (2.23) and the trivial relation (2.24), with `𝔖(h) ≥ 1`.
* Assembly `modulus_real_large`: (2.28) and (2.29) give `r_i' → ∞` for real characters.
* Assembly `modulus_nonreal_large`: (2.30) gives `log(2 r_i') → ∞`, the content of (2.31).

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Linnik.Decomp1537b

open Finset Real
open Filter Asymptotics

/-! ### `I(h)` and `I(h, ϱ, ϱ')`, (2.16) and (2.17), p. 4 -/

/-- `I(h) = #{m, ℓ ∈ (N₁, N) : m - ℓ = h}`, (2.17) p. 4, counted by `m`. -/
def I1 (N N1 : ℕ) (h : ℤ) : ℕ :=
  ((Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N)).card

/-- `I(h, ϱ, ϱ') = ∑_{m, ℓ ∈ (N₁, N), m - ℓ = h} m^{ϱ - 1} ℓ^{ϱ' - 1}`, (2.16) p. 4. -/
noncomputable def Irho (N N1 : ℕ) (h : ℤ) (ρ ρ' : ℂ) : ℂ :=
  ∑ m ∈ (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N),
    (m : ℂ) ^ (ρ - 1) * (((m : ℤ) - h : ℤ) : ℂ) ^ (ρ' - 1)

/-- LEAF. Unit U-1537. `I(h) ≤ N`, since `m` runs over at most `N - N₁ - 1` integers; used with
(2.24) p. 5 to bound the non principal pairs in (2.19) p. 4. -/
theorem I1_le (N N1 : ℕ) (h : ℤ) : (I1 N N1 h : ℝ) ≤ N := by
  have h1 : I1 N N1 h = ((Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N)).card := rfl
  have h2 : ((Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N)).card ≤ (Ico 0 N).card := by
    apply card_le_card
    intro x hx
    rw [mem_filter] at hx
    rw [mem_Ioo] at hx
    rw [mem_Ico]
    exact ⟨by positivity, hx.1.2⟩
  have h3 : (Ico 0 N).card = N := Nat.card_Ico 0 N
  have h4 : I1 N N1 h ≤ N := by
    calc I1 N N1 h ≤ (Ico 0 N).card := h2
         _ = N := h3
  exact Nat.cast_le.mpr h4

/-- LEAF. Unit U-1537. (2.17) p. 4: `I(h) = N - |h| + O(N₁)`, in the explicit form
`|I(h) - N| ≤ |h| + N₁ + 1`; here `N₁ = N^{1-ε}` of (2.1) p. 3. -/
theorem abs_I1_sub (N N1 : ℕ) (h : ℤ) : |(I1 N N1 h : ℝ) - N| ≤ |(h : ℝ)| + N1 + 1 := by
  have hcount : N - (N1 + h.natAbs) - 1 ≤ I1 N N1 h := by
    by_cases hh : 0 ≤ h
    · have ha : (h.natAbs : ℤ) = h := Int.natAbs_of_nonneg hh
      have hsub : Ioo (N1 + h.natAbs) N ⊆
          (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N) := by
        intro m hm
        simp only [mem_Ioo, mem_filter] at *
        omega
      simpa [I1, Nat.card_Ioo] using card_le_card hsub
    · have ha : (h.natAbs : ℤ) = -h := by rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]
      have hsub : Ioo N1 (N - h.natAbs) ⊆
          (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N) := by
        intro m hm
        simp only [mem_Ioo, mem_filter] at *
        omega
      have hc := card_le_card hsub
      simp only [Nat.card_Ioo] at hc
      simpa [I1, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc
  have hn : N ≤ I1 N N1 h + N1 + h.natAbs + 1 := by omega
  have hr : (N : ℝ) ≤ (I1 N N1 h : ℝ) + N1 + h.natAbs + 1 := by exact_mod_cast hn
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [abs_of_nonpos (sub_nonpos.mpr (I1_le N N1 h))]
  rw [habs] at hr
  linarith

/-- LEAF. Unit U-1537. The trivial relation (2.24) p. 5: if `Re ϱ ≤ 1` and `Re ϱ' ≤ 1` then
`|I(h, ϱ, ϱ')| ≤ I(h)`, since `|m^{ϱ-1}| = m^{Re ϱ - 1} ≤ 1` for `m ≥ 1`. -/
theorem norm_Irho_le (N N1 : ℕ) (h : ℤ) {ρ ρ' : ℂ} (hρ : ρ.re ≤ 1) (hρ' : ρ'.re ≤ 1) :
    ‖Irho N N1 h ρ ρ'‖ ≤ I1 N N1 h := by
  unfold Irho I1
  calc
    ‖∑ m ∈ (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N),
      (m : ℂ) ^ (ρ - 1) * (((m : ℤ) - h : ℤ) : ℂ) ^ (ρ' - 1)‖
        ≤ ∑ m ∈ (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N),
            ‖(m : ℂ) ^ (ρ - 1) * (((m : ℤ) - h : ℤ) : ℂ) ^ (ρ' - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N), (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      obtain ⟨hm, hmh⟩ := mem_filter.mp hm
      obtain ⟨hm0, hmN⟩ := mem_Ioo.mp hm
      have hm1 : 1 ≤ m := by omega
      have hmh1 : (1 : ℤ) ≤ (m : ℤ) - h := by omega
      have hz : 0 < (((m : ℤ) - h : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < (m : ℤ) - h)
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < m)]
      have heq : (((m : ℤ) - h : ℤ) : ℂ) = ((((m : ℤ) - h : ℤ) : ℝ) : ℂ) := by norm_cast
      rw [heq, Complex.norm_cpow_eq_rpow_re_of_pos hz]
      apply mul_le_one₀
      · apply Real.rpow_le_one_of_one_le_of_nonpos
        · exact_mod_cast hm1
        · simpa using sub_nonpos.mpr hρ
      · positivity
      · apply Real.rpow_le_one_of_one_le_of_nonpos
        · exact_mod_cast hmh1
        · simpa using sub_nonpos.mpr hρ'
    _ = _ := by simp

/-- LEAF. Unit U-1537. For `ϱ_i = ϱ_j = 1`, the pole, `I(h, 1, 1) = I(h)`, (2.17) p. 4. -/
theorem Irho_one_one (N N1 : ℕ) (h : ℤ) : Irho N N1 h 1 1 = I1 N N1 h := by
  simp [Irho, I1]

/-! ### Corollary 1 from Theorem 2, p. 5 -/

/-- **(2.25) of Corollary 1, p. 5, from Theorem 2, p. 4. A real proof, no leaves needed beyond
its hypotheses.** Index the generalized exceptional singularities by `Fin (M + 1)`, `0` being the
pole `ϱ = 1`. Suppose, as in (2.19) with (2.22), `|R₁(h) - ∑_{i,j} 𝔖(χ_i, χ_j, h) A(ϱ_i) A(ϱ_j)
I(h, ϱ_i, ϱ_j)| ≤ εN/2`; that `𝔖(χ₀, χ₀, h) = 𝔖(h)` and every other pair has
`|𝔖(χ_i, χ_j, h)| ≤ ε₀ = ε/(6(M+1)²)`, which is (2.20) with (2.23) when no `r_i | C(ε₀) h`,
(2.26); `|A| = 1`, (2.18); `|I(h, ϱ_i, ϱ_j)| ≤ I(h) ≤ N`, (2.24) with `I1_le`; and (2.17) in the
form of `abs_I1_sub`. Then for `|h| ≤ εN/4`, `N₁ + 1 ≤ εN/12` and `𝔖(h) ≥ 1`,
`|R₁(h) - 𝔖(h) N| ≤ ε 𝔖(h) N`, which is (2.25). The paper's `𝔖(h) ≥ 2C₀ ≈ 1.32` for `h ≠ 0`. -/
theorem cor1_of_thm2 {M : ℕ} {N N1 ε ε0 Sig I h : ℝ} {R : ℂ}
    (S : Fin (M + 1) → Fin (M + 1) → ℂ) (A : Fin (M + 1) → ℝ)
    (J : Fin (M + 1) → Fin (M + 1) → ℂ)
    (hε : 0 < ε) (hN : 0 < N) (hSig : 1 ≤ Sig)
    (hε0 : ε0 = ε / (6 * ((M : ℝ) + 1) ^ 2))
    (hS00 : S 0 0 = Sig) (hSij : ∀ i j, ¬ (i = 0 ∧ j = 0) → ‖S i j‖ ≤ ε0)
    (hA : ∀ i, |A i| = 1) (hA0 : A 0 = 1)
    (hJ00 : J 0 0 = I) (hJ : ∀ i j, ‖J i j‖ ≤ I) (hIN : I ≤ N)
    (hIh : |I - N| ≤ |h| + N1 + 1) (hh : |h| ≤ ε * N / 4) (hN1 : N1 + 1 ≤ ε * N / 12)
    (hR : ‖R - ∑ i, ∑ j, S i j * A i * A j * J i j‖ ≤ ε * N / 2) :
    ‖R - Sig * N‖ ≤ ε * Sig * N := by
  have hI0 : 0 ≤ I := le_trans (norm_nonneg _) (hJ 0 0)
  have hε0nn : 0 ≤ ε0 := by rw [hε0]; positivity
  have hAn : ∀ i, ‖((A i : ℝ) : ℂ)‖ = 1 := fun i => by
    rw [Complex.norm_real, Real.norm_eq_abs, hA]
  have key : ∀ i j, ‖S i j * A i * A j * J i j -
      (if i = 0 ∧ j = 0 then ((Sig : ℂ) * I) else 0)‖ ≤ ε0 * I := by
    intro i j
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, if_true, hS00, hA0, hJ00, Complex.ofReal_one, mul_one, sub_self,
        norm_zero]
      positivity
    · rw [if_neg hij, sub_zero, norm_mul, norm_mul, norm_mul, hAn, hAn, mul_one, mul_one]
      exact mul_le_mul (hSij i j hij) (hJ i j) (norm_nonneg _) hε0nn
  have hsumite : ∑ i : Fin (M + 1), ∑ j : Fin (M + 1),
      (if i = 0 ∧ j = 0 then ((Sig : ℂ) * I) else 0) = (Sig : ℂ) * I := by
    simp [ite_and]
  have hdiff : ‖∑ i, ∑ j, S i j * A i * A j * J i j - (Sig : ℂ) * I‖ ≤
      ((M : ℝ) + 1) ^ 2 * (ε0 * I) := by
    rw [← hsumite]
    have hsplit : ∑ i, ∑ j, S i j * A i * A j * J i j -
        ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (if i = 0 ∧ j = 0 then ((Sig : ℂ) * I) else 0) =
        ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (S i j * A i * A j * J i j -
          (if i = 0 ∧ j = 0 then ((Sig : ℂ) * I) else 0)) := by
      simp only [← Finset.sum_sub_distrib]
    rw [hsplit]
    calc ‖∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (S i j * A i * A j * J i j -
          (if i = 0 ∧ j = 0 then ((Sig : ℂ) * I) else 0))‖
        ≤ ∑ i : Fin (M + 1), ‖∑ j : Fin (M + 1), (S i j * A i * A j * J i j -
          (if i = 0 ∧ j = 0 then ((Sig : ℂ) * I) else 0))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ‖S i j * A i * A j * J i j -
          (if i = 0 ∧ j = 0 then ((Sig : ℂ) * I) else 0)‖ :=
          sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ε0 * I :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => key i j
      _ = ((M : ℝ) + 1) ^ 2 * (ε0 * I) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hM : ((M : ℝ) + 1) ^ 2 * (ε0 * I) ≤ ε * N / 6 := by
    rw [hε0]
    have hMpos : 0 < ((M : ℝ) + 1) ^ 2 := by positivity
    have : ((M : ℝ) + 1) ^ 2 * (ε / (6 * ((M : ℝ) + 1) ^ 2) * I) = ε * I / 6 := by
      field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_left hIN hε.le
    linarith
  have hSigpos : 0 < Sig := lt_of_lt_of_le one_pos hSig
  have hSigIN : ‖(Sig : ℂ) * I - Sig * N‖ ≤ Sig * (ε * N / 3) := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hSigpos,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ hSigpos.le
    linarith
  have t1 := norm_sub_le_norm_sub_add_norm_sub R (∑ i, ∑ j, S i j * A i * A j * J i j)
    ((Sig : ℂ) * N)
  have t2 := norm_sub_le_norm_sub_add_norm_sub (∑ i, ∑ j, S i j * A i * A j * J i j)
    ((Sig : ℂ) * I) ((Sig : ℂ) * N)
  have hεN : 0 ≤ ε * N := by positivity
  have h3 : ε * N ≤ ε * N * Sig := by nlinarith
  linarith

/-! ### The exceptional moduli grow, (2.27) to (2.32), pp. 5 and 6 -/

/-- LEAF. Unit U-1537. (2.29) p. 6, the arithmetic: a zero `1 - δ` with `δ ≤ H/log N`, (2.12)
p. 3, and a lower bound `δ ≥ c/√r` for a real primitive character mod `r`, by [Pin1] or [GS],
give `r ≥ (c log N/H)²`, i.e. `r ≫ L²`. Here `lN` stands for `log N`. -/
theorem real_case {r δ H c lN : ℝ} (hr : 0 < r) (hc : 0 < c) (hH : 0 < H) (hlN : 0 < lN)
    (hδ : δ ≤ H / lN) (hlow : c / Real.sqrt r ≤ δ) : (c * lN / H) ^ 2 ≤ r := by
  have h1 : c / Real.sqrt r ≤ H / lN := hlow.trans hδ
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h2 : c * lN / H ≤ Real.sqrt r := by
    rw [div_le_iff₀ hsqrt] at h1
    have h1_mul : c * lN ≤ Real.sqrt r * H := by
      calc c * lN ≤ (H / lN * Real.sqrt r) * lN := mul_le_mul_of_nonneg_right h1 (le_of_lt hlN)
           _ = Real.sqrt r * H := by
             calc (H / lN * Real.sqrt r) * lN = H / lN * lN * Real.sqrt r := by ring
                  _ = H * Real.sqrt r := by rw [div_mul_cancel₀ _ (ne_of_gt hlN)]
                  _ = Real.sqrt r * H := mul_comm _ _
    rw [div_le_iff₀ hH]
    exact h1_mul
  have h3 : (c * lN / H) ^ 2 ≤ (Real.sqrt r) ^ 2 := by
    apply pow_le_pow_left₀
    · positivity
    · exact h2
  rw [Real.sq_sqrt (le_of_lt hr)] at h3
  exact h3

/-- LEAF. Unit U-1537. (2.30) to (2.31) pp. 5 and 6, the arithmetic: if a zero with
`σ ≥ 1 - H/log N` lies outside Iwaniec's zero free region, so that
`1/(4·10⁴ (x + (ℓ log ℓ)^{3/4})) ≤ H/log N` with `x = log(2r')`, and `1 ≤ ℓ ≤ 2 log N`, then
`x ≥ log N/(8·10⁴ H)` once `log N` is large; the term `(ℓ log ℓ)^{3/4} = o(log N)` is absorbed.
Here `lN` stands for `log N`. -/
theorem nonreal_case {H : ℝ} (hH : 0 < H) :
    ∃ Y : ℝ, ∀ lN : ℝ, Y ≤ lN → ∀ x ℓ : ℝ, Real.log 2 ≤ x → 1 ≤ ℓ → ℓ ≤ 2 * lN →
      1 / (4 * 10 ^ 4 * (x + (ℓ * Real.log ℓ) ^ ((3 : ℝ) / 4))) ≤ H / lN →
      lN / (8 * 10 ^ 4 * H) ≤ x := by
  have hsmall : (fun z : ℝ => (z * log z) ^ ((3 : ℝ) / 4)) =o[atTop] fun z => z := by
    have ho := (isLittleO_log_rpow_rpow_atTop ((3 : ℝ) / 4) (by norm_num : (0 : ℝ) < 1 / 4)).mul_isBigO
      (Asymptotics.isBigO_refl (fun z : ℝ => z ^ ((3 : ℝ) / 4)) atTop)
    apply ho.congr'
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      rw [Real.mul_rpow (by linarith : 0 ≤ z) (Real.log_nonneg hz), mul_comm]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      rw [← Real.rpow_add hz]
      norm_num
  have hc : 0 < 1 / (16 * 10 ^ 4 * H) := by positivity
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp (hsmall.bound hc)
  refine ⟨max 1 (Z / 2), ?_⟩
  intro lN hlN x ℓ hx hℓ hℓN hrec
  have hN : 1 ≤ lN := le_trans (le_max_left _ _) hlN
  have hZ2 : Z ≤ 2 * lN := by have := le_trans (le_max_right _ _) hlN; linarith
  have hf := hZ (2 * lN) hZ2
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by nlinarith [Real.log_nonneg (show 1 ≤ 2 * lN by linarith)]) _),
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 2 * lN)] at hf
  have hmono : (ℓ * log ℓ) ^ ((3 : ℝ) / 4) ≤ (2 * lN * log (2 * lN)) ^ ((3 : ℝ) / 4) := by
    apply Real.rpow_le_rpow (mul_nonneg (by linarith) (Real.log_nonneg hℓ)) _ (by norm_num)
    exact mul_le_mul hℓN (Real.log_le_log (by linarith) hℓN) (Real.log_nonneg hℓ) (by linarith)
  have htail : (ℓ * log ℓ) ^ ((3 : ℝ) / 4) ≤ lN / (8 * 10 ^ 4 * H) := by
    calc _ ≤ (2 * lN * log (2 * lN)) ^ ((3 : ℝ) / 4) := hmono
         _ ≤ 1 / (16 * 10 ^ 4 * H) * (2 * lN) := hf
         _ = lN / (8 * 10 ^ 4 * H) := by ring
  have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hx
  have hp : 0 ≤ (ℓ * log ℓ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hℓ)) _
  have hden : 0 < 4 * 10 ^ 4 * (x + (ℓ * log ℓ) ^ ((3 : ℝ) / 4)) := by positivity
  have hcross := (div_le_div_iff₀ hden (by linarith : 0 < lN)).mp hrec
  have htail' := (le_div_iff₀ (by positivity : 0 < 8 * 10 ^ 4 * H)).mp htail
  rw [div_le_iff₀ (by positivity : 0 < 8 * 10 ^ 4 * H)]
  nlinarith

/-- LEAF. Unit U-1537. `ℓ_i = log(r_i(|t| + 2)) ≤ 2 log N` for `r_i ≤ P ≤ N` and `|t| ≤ √N`,
(2.12) p. 3 and (2.30) p. 6, once `N ≥ 4`. -/
theorem ell_le {N r t : ℝ} (hN : 4 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N) (ht : |t| ≤ Real.sqrt N) :
    Real.log (r * (|t| + 2)) ≤ 2 * Real.log N := by
  have hs : Real.sqrt N ≤ N - 2 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  calc
    Real.log (r * (|t| + 2)) ≤ Real.log (N ^ 2) := by
      apply Real.log_le_log (by positivity)
      calc r * (|t| + 2) ≤ N * N := mul_le_mul hrN (by linarith) (by positivity) (by linarith)
           _ = N ^ 2 := by ring
    _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num

/-- **Real exceptional characters, (2.28) and (2.29) p. 5 and 6. CONDITIONAL ON `real_case`.**
If `χ_i` is real primitive mod `r_i = A_i r_i'` with `A_i ∈ {1, 4, 8}`, (2.28), and its zero
satisfies `c/√r_i ≤ δ_i ≤ H/log N`, then `r_i' ≥ T` once `log N ≥ Y(T)`: the odd squarefree
part tends to infinity, (2.27) and (2.32). -/
theorem modulus_real_large {c H : ℝ} (hc : 0 < c) (hH : 0 < H) (T : ℝ) :
    ∃ Y : ℝ, ∀ lN : ℝ, Y ≤ lN → ∀ r r' δ A : ℝ, r = A * r' → (A = 1 ∨ A = 4 ∨ A = 8) →
      0 < r' → δ ≤ H / lN → c / Real.sqrt r ≤ δ → T ≤ r' := by
  refine ⟨H * (8 * |T| + 1) / c + 1, ?_⟩
  intro lN hY r r' δ A hrA hA hr' hδ hlow
  have hApos : 0 < A ∧ A ≤ 8 := by rcases hA with rfl | rfl | rfl <;> norm_num
  have hr : 0 < r := by rw [hrA]; exact mul_pos hApos.1 hr'
  have hY0 : 0 ≤ H * (8 * |T| + 1) / c := by positivity
  have hlN : 0 < lN := by linarith
  have h1 := real_case hr hc hH hlN hδ hlow
  have h2 : 8 * |T| + 1 ≤ c * lN / H := by
    rw [le_div_iff₀ hH]
    have h5 : H * (8 * |T| + 1) / c ≤ lN := by linarith
    rw [div_le_iff₀ hc] at h5
    linarith
  have hT0 := abs_nonneg T
  have h3 : 8 * |T| + 1 ≤ (c * lN / H) ^ 2 := by nlinarith
  have h4 : r ≤ 8 * r' := by rw [hrA]; nlinarith [hApos.2]
  have h6 : |T| ≤ r' := by linarith
  exact le_trans (le_abs_self T) h6

/-- **Non real exceptional characters, (2.30) and (2.31) pp. 5 and 6. CONDITIONAL ON
`nonreal_case` and `ell_le`.** If `χ_i` mod `r_i ∈ [3, N]` has a zero `σ + it`, `|t| ≤ √N`, with
`σ ≥ 1 - H/log N`, (2.12), and the zero lies outside Iwaniec's region (2.30), i.e.
`σ ≤ 1 - 1/(4·10⁴(log(2r_i') + (ℓ_i log ℓ_i)^{3/4}))`, then `log(2 r_i') ≥ T` once `log N` is
large. So `r_i' → ∞`, which is what (2.27) and the Remark (2.32) need. -/
theorem modulus_nonreal_large {H : ℝ} (hH : 0 < H) (T : ℝ) :
    ∃ Y : ℝ, ∀ N : ℝ, 4 ≤ N → Y ≤ Real.log N → ∀ r' r t σ : ℝ, 1 ≤ r' → 3 ≤ r → r ≤ N →
      |t| ≤ Real.sqrt N → 1 - H / Real.log N ≤ σ →
      σ ≤ 1 - 1 / (4 * 10 ^ 4 * (Real.log (2 * r') +
        (Real.log (r * (|t| + 2)) * Real.log (Real.log (r * (|t| + 2)))) ^ ((3 : ℝ) / 4))) →
      T ≤ Real.log (2 * r') := by
  obtain ⟨Y0, hY0⟩ := nonreal_case hH
  refine ⟨max Y0 (8 * 10 ^ 4 * H * T), ?_⟩
  intro N hN hY r' r t σ hr' hr hrN ht hσ1 hσ2
  have hYa : Y0 ≤ Real.log N := le_trans (le_max_left _ _) hY
  have hYb : 8 * 10 ^ 4 * H * T ≤ Real.log N := le_trans (le_max_right _ _) hY
  have hx : Real.log 2 ≤ Real.log (2 * r') :=
    Real.log_le_log (by norm_num) (by linarith)
  have hℓ1 : 1 ≤ Real.log (r * (|t| + 2)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    have : 6 ≤ r * (|t| + 2) := by nlinarith [abs_nonneg t]
    linarith
  have hℓ2 := ell_le hN (by linarith) hrN ht
  have hineq : 1 / (4 * 10 ^ 4 * (Real.log (2 * r') +
      (Real.log (r * (|t| + 2)) * Real.log (Real.log (r * (|t| + 2)))) ^ ((3 : ℝ) / 4))) ≤
      H / Real.log N := by linarith
  have hmain := hY0 (Real.log N) hYa (Real.log (2 * r')) (Real.log (r * (|t| + 2))) hx hℓ1 hℓ2
    hineq
  have hden : 0 < 8 * 10 ^ 4 * H := by positivity
  have : T ≤ Real.log N / (8 * 10 ^ 4 * H) := by
    rw [le_div_iff₀ hden]
    linarith
  linarith

/-- The pair condition (2.21) p. 4 against (2.26) p. 5: if `r_i ∤ C h` then
`[r_i, r_j] ∤ C h`, so every pair other than the pole pair falls under (2.20). Proved. -/
theorem lcm_not_dvd_of_left {a b n : ℕ} (h : ¬ a ∣ n) : ¬ Nat.lcm a b ∣ n :=
  fun hl => h ((Nat.dvd_lcm_left a b).trans hl)

/-- P0035 p.4 display 2.17. Exact count for the open interval, with natural subtraction. -/
theorem I1_eq_sub (N N1 : ℕ) (h : ℤ) : I1 N N1 h = N - (N1 + h.natAbs) - 1 := by
  unfold I1
  by_cases hh : 0 ≤ h
  · have ha : (h.natAbs : ℤ) = h := Int.natAbs_of_nonneg hh
    have heq : (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N) =
        Ioo (N1 + h.natAbs) N := by
      ext m
      simp only [mem_filter, mem_Ioo]
      omega
    rw [heq, Nat.card_Ioo]
  · have ha : (h.natAbs : ℤ) = -h := by rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]
    have heq : (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N) =
        Ioo N1 (N - h.natAbs) := by
      ext m
      simp only [mem_filter, mem_Ioo]
      omega
    rw [heq, Nat.card_Ioo]
    omega

/-- P0035 p.4 display 2.17. The printed main term has endpoint error at most N1 plus one. -/
theorem abs_I1_sub_main (N N1 : ℕ) (h : ℤ) (hh : |(h : ℝ)| ≤ N) :
    |(I1 N N1 h : ℝ) - ((N : ℝ) - |(h : ℝ)|)| ≤ (N1 : ℝ) + 1 := by
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  by_cases hlarge : N1 + h.natAbs + 1 ≤ N
  · have hn : I1 N N1 h + N1 + h.natAbs + 1 = N := by rw [I1_eq_sub]; omega
    have hr : (I1 N N1 h : ℝ) + N1 + h.natAbs + 1 = N := by exact_mod_cast hn
    rw [habs] at hr
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hz : I1 N N1 h = 0 := by rw [I1_eq_sub]; omega
    have hn : N ≤ N1 + h.natAbs + 1 := by omega
    have hr : (N : ℝ) ≤ N1 + h.natAbs + 1 := by exact_mod_cast hn
    rw [habs] at hr
    rw [hz, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (sub_nonneg.mpr hh)]
    linarith

/-- P0035 p.4 display 2.16. The encoded weighted sum equals the two variable interval sum. -/
theorem Irho_eq_double_sum (N N1 : ℕ) (h : ℤ) (ρ ρ' : ℂ) :
    Irho N N1 h ρ ρ' = ∑ m ∈ Ioo N1 N, ∑ ℓ ∈ Ioo N1 N,
      if (m : ℤ) - ℓ = h then (m : ℂ) ^ (ρ - 1) * (ℓ : ℂ) ^ (ρ' - 1) else 0 := by
  classical
  unfold Irho
  rw [sum_filter]
  apply sum_congr rfl
  intro m hm
  by_cases ha : (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N
  · rw [ite_eq_left ha]
    let ℓ : ℕ := ((m : ℤ) - h).toNat
    have hℓ : (ℓ : ℤ) = (m : ℤ) - h := Int.toNat_of_nonneg (by omega)
    have hmem : ℓ ∈ Ioo N1 N := by rw [mem_Ioo]; omega
    rw [sum_eq_single ℓ]
    · have heq : (m : ℤ) - ℓ = h := by omega
      rw [ite_eq_left heq]
      congr 2
      exact_mod_cast hℓ.symm
    · intro j hj hjℓ
      have hne : (m : ℤ) - j ≠ h := by omega
      rw [ite_eq_right hne]
    · exact fun hn => (hn hmem).elim
  · rw [ite_eq_right ha]
    symm
    apply sum_eq_zero
    intro ℓ hℓ
    have hℓ' := mem_Ioo.mp hℓ
    have hne : (m : ℤ) - ℓ ≠ h := by omega
    rw [ite_eq_right hne]

/-- P0035 p.4 display 2.16. Swapping the two interval variables reverses the difference. -/
theorem Irho_neg_swap (N N1 : ℕ) (h : ℤ) (ρ ρ' : ℂ) : Irho N N1 (-h) ρ' ρ = Irho N N1 h ρ ρ' := by
  rw [Irho_eq_double_sum, Irho_eq_double_sum, sum_comm]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro ℓ hℓ
  have heq : (ℓ : ℤ) - m = -h ↔ (m : ℤ) - ℓ = h := by omega
  simp only [heq, mul_comm]

/-- P0035 p.5 Corollary 1. CONDITIONAL ON the supplied explicit formula and singular series estimates. The interval bounds and pole identity are discharged. -/
theorem cor1_of_Irho {M N N1 : ℕ} {h : ℤ} {ε ε0 Sig : ℝ} {R : ℂ}
    (S : Fin (M + 1) → Fin (M + 1) → ℂ) (A : Fin (M + 1) → ℝ)
    (ρ : Fin (M + 1) → ℂ)
    (hε : 0 < ε) (hN : 0 < N) (hSig : 1 ≤ Sig)
    (hε0 : ε0 = ε / (6 * ((M : ℝ) + 1) ^ 2))
    (hS00 : S 0 0 = Sig) (hSij : ∀ i j, ¬ (i = 0 ∧ j = 0) → ‖S i j‖ ≤ ε0)
    (hA : ∀ i, |A i| = 1) (hA0 : A 0 = 1)
    (hρ0 : ρ 0 = 1) (hρ : ∀ i, (ρ i).re ≤ 1)
    (hh : |(h : ℝ)| ≤ ε * N / 4) (hN1 : (N1 : ℝ) + 1 ≤ ε * N / 12)
    (hR : ‖R - ∑ i, ∑ j, S i j * A i * A j * Irho N N1 h (ρ i) (ρ j)‖ ≤ ε * N / 2) :
    ‖R - Sig * N‖ ≤ ε * Sig * N := by
  apply cor1_of_thm2 (I := (I1 N N1 h : ℝ)) (h := (h : ℝ)) S A (fun i j => Irho N N1 h (ρ i) (ρ j))
    hε (Nat.cast_pos.mpr hN) hSig hε0 hS00 hSij hA hA0
  · rw [hρ0, Irho_one_one]; norm_cast
  · exact fun i j => norm_Irho_le N N1 h (hρ i) (hρ j)
  · exact I1_le N N1 h
  · exact abs_I1_sub N N1 h
  · exact hh
  · exact hN1
  · exact hR

/-- P0035 pp.5 and 6 displays 2.28 and 2.29. Scalar conductor rate from the supplied zero bounds. -/
theorem real_conductor_rate {c H lN r r' δ A : ℝ} (hc : 0 < c) (hH : 0 < H) (hlN : 0 < lN)
    (hrA : r = A * r') (hA : A = 1 ∨ A = 4 ∨ A = 8) (hr' : 0 < r')
    (hδ : δ ≤ H / lN) (hlow : c / Real.sqrt r ≤ δ) :
    (c * lN / H) ^ 2 / 8 ≤ r' := by
  have hApos : 0 < A ∧ A ≤ 8 := by rcases hA with rfl | rfl | rfl <;> norm_num
  have hr : 0 < r := by rw [hrA]; exact mul_pos hApos.1 hr'
  have hh := real_case hr hc hH hlN hδ hlow
  have hb : r ≤ 8 * r' := by rw [hrA]; exact mul_le_mul_of_nonneg_right hApos.2 hr'.le
  linarith

/-- P0035 p.6 displays 2.30 and 2.31. Scalar power growth from the supplied zero location bounds. -/
theorem nonreal_conductor_power {H : ℝ} (hH : 0 < H) :
    ∃ Y : ℝ, ∀ N : ℝ, 4 ≤ N → Y ≤ Real.log N → ∀ r' r t σ : ℝ, 1 ≤ r' → 3 ≤ r → r ≤ N →
      |t| ≤ Real.sqrt N → 1 - H / Real.log N ≤ σ →
      σ ≤ 1 - 1 / (4 * 10 ^ 4 * (Real.log (2 * r') +
        (Real.log (r * (|t| + 2)) * Real.log (Real.log (r * (|t| + 2)))) ^ ((3 : ℝ) / 4))) →
      N ^ (1 / (8 * 10 ^ 4 * H)) ≤ 2 * r' := by
  obtain ⟨Y0, hY0⟩ := nonreal_case hH
  refine ⟨Y0, ?_⟩
  intro N hN hYa r' r t σ hr' hr hrN ht hσ1 hσ2
  have hx : Real.log 2 ≤ Real.log (2 * r') :=
    Real.log_le_log (by norm_num) (by linarith)
  have hℓ1 : 1 ≤ Real.log (r * (|t| + 2)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    have : 6 ≤ r * (|t| + 2) := by nlinarith [abs_nonneg t]
    linarith
  have hℓ2 := ell_le hN (by linarith) hrN ht
  have hineq : 1 / (4 * 10 ^ 4 * (Real.log (2 * r') +
      (Real.log (r * (|t| + 2)) * Real.log (Real.log (r * (|t| + 2)))) ^ ((3 : ℝ) / 4))) ≤
      H / Real.log N := by linarith
  have hmain := hY0 (Real.log N) hYa (Real.log (2 * r')) (Real.log (r * (|t| + 2))) hx hℓ1 hℓ2
    hineq
  have he := Real.exp_le_exp.mpr hmain
  rw [Real.exp_log (by positivity : 0 < 2 * r')] at he
  rw [Real.rpow_def_of_pos (by linarith : 0 < N)]
  simpa only [div_eq_mul_inv, one_div, one_mul] using he

/-- P0035 pp.2 and 5 displays 2.1 and 2.22. The power cutoff and endpoint error are uniformly small. -/
theorem cutoff_small {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (N : ℝ) ^ (1 - κ) + 1 ≤ ε * N / 12 := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-κ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - κ) + 1 ≤ ε * N / 12 := by
    filter_upwards [ht.eventually (ge_mem_nhds (by positivity : 0 < ε / 24)),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (24 / ε), eventually_ge_atTop 1] with N hp hN hN1
    have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hr : (N : ℝ) ^ (1 - κ) = N * (N : ℝ) ^ (-κ) := by
      rw [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one]
    have hlarge : 24 ≤ (N : ℝ) * ε := (div_le_iff₀ hε).mp hN
    have hh := mul_le_mul_of_nonneg_left hp hpos.le
    rw [hr]
    nlinarith
  exact eventually_atTop.mp he

/-- P0035 pp.2, 4 and 5. A common cutoff threshold for Corollary 1, CONDITIONAL ON the supplied explicit formula and singular series estimates at each N. -/
theorem cor1_for_large_N {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ N1 : ℕ, (N1 : ℝ) ≤ (N : ℝ) ^ (1 - κ) →
      ∀ h : ℤ, |(h : ℝ)| ≤ ε * N / 4 → ∀ M : ℕ, ∀ (Sig : ℝ) (R : ℂ)
        (S : Fin (M + 1) → Fin (M + 1) → ℂ) (A : Fin (M + 1) → ℝ)
        (ρ : Fin (M + 1) → ℂ),
      1 ≤ Sig → S 0 0 = Sig →
      (∀ i j, ¬ (i = 0 ∧ j = 0) → ‖S i j‖ ≤ ε / (6 * ((M : ℝ) + 1) ^ 2)) →
      (∀ i, |A i| = 1) → A 0 = 1 → ρ 0 = 1 → (∀ i, (ρ i).re ≤ 1) →
      ‖R - ∑ i, ∑ j, S i j * A i * A j * Irho N N1 h (ρ i) (ρ j)‖ ≤ ε * N / 2 →
      ‖R - Sig * N‖ ≤ ε * Sig * N := by
  obtain ⟨N0, hN0⟩ := cutoff_small hκ hε
  refine ⟨max N0 1, ?_⟩
  intro N hN N1 hcut h hh M Sig R S A ρ hSig hS00 hSij hA hA0 hρ0 hρ hR
  have hNlarge : N0 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by have := (le_max_right N0 1).trans hN; omega
  have hN1 : (N1 : ℝ) + 1 ≤ ε * N / 12 := (by linarith : (N1 : ℝ) + 1 ≤ (N : ℝ) ^ (1 - κ) + 1).trans (hN0 N hNlarge)
  exact cor1_of_Irho S A ρ hε hNpos hSig rfl hS00 hSij hA hA0 hρ0 hρ hh hN1 hR

/-- P0035 pp.5 and 6 displays 2.27 through 2.32. A common scalar growth threshold for the supplied real or nonreal zero bounds. -/
theorem modulus_growth_of_alternatives {c H : ℝ} (hc : 0 < c) (hH : 0 < H) (T : ℝ) :
    ∃ Y : ℝ, ∀ N : ℝ, 4 ≤ N → Y ≤ Real.log N → ∀ r' r t σ : ℝ,
      1 ≤ r' → r ≤ N → |t| ≤ Real.sqrt N → 1 - H / Real.log N ≤ σ →
      ((∃ A : ℝ, r = A * r' ∧ (A = 1 ∨ A = 4 ∨ A = 8) ∧ c / Real.sqrt r ≤ 1 - σ) ∨
        (3 ≤ r ∧ σ ≤ 1 - 1 / (4 * 10 ^ 4 * (Real.log (2 * r') +
          (Real.log (r * (|t| + 2)) * Real.log (Real.log (r * (|t| + 2)))) ^ ((3 : ℝ) / 4))))) →
      T ≤ r' := by
  obtain ⟨Yr, hYr⟩ := modulus_real_large hc hH T
  obtain ⟨Yn, hYn⟩ := modulus_nonreal_large hH (Real.log (2 * max T 1))
  refine ⟨max Yr Yn, ?_⟩
  intro N hN hY r' r t σ hr' hrN ht hσ hcase
  rcases hcase with ⟨A, hrA, hA, hlow⟩ | ⟨hr, hupper⟩
  · exact hYr (Real.log N) ((le_max_left _ _).trans hY) r r' (1 - σ) A hrA hA
      (by linarith) (by linarith) hlow
  · have hlog := hYn N hN ((le_max_right _ _).trans hY) r' r t σ hr' hr hrN ht hσ hupper
    have hp : 0 < 2 * max T 1 := by have := le_max_right T 1; positivity
    have hmul := (Real.log_le_log_iff hp (by positivity : 0 < 2 * r')).mp hlog
    have hT := le_max_left T 1
    linarith

end LeanLab.Linnik.Decomp1537b
