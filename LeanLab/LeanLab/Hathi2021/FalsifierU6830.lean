/-
U-6830, falsifier, CLOUD 20261020T2317Z-cloud53. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

Independent falsifier check of the U-6827 QUESTION on P0080, Hathi arXiv 2109.13174,
Lemma 3.1 page 9 against display 2.10 page 7, and of the U-6827 QUESTION on the kappa value
3/2 for 15 | h in P0101 page 197 and P0102 page 88.

What is here:
* `cntF`, Hathi's `N_l(d)` of display 2.7 as a count of tuples, with the recursion
  `cntF_succ` and a memo table `tab` proved equal to it, `cntF_eq_tab`.
* `N5_15 : N_5(15) = 70588` and `N5_3 : N_5(3) = 342`, from the definition, by kernel
  evaluation of the proved table.
* `d1_terms`: the two `d = 1` terms of 2.10 at `l = 5` give exactly `8419335/8388608 > 1`.
* `hathi_c05_ge`: for any nonnegative summable families with those `d = 1` terms, the
  2.10 combination is at least `8419335/8388608`, above the printed `0.7773`.
* `k30_fails_of`: the section 4 criterion at `l = 5` fails at `k' = 30` for every
  `c ≥ 0.9537`; `k31_ok_of`: it holds at `k' = 31` for every `c ≤ 1.07`.
* `factor5_dvd`: the local factor at `p = 5`, `5 ∣ h`, from the papers' own table of
  `B(p, h)` is `15/8`, not `3/2`.
-/
import Mathlib

namespace LeanLab.Hathi2021.FalsifierU6830

open Finset

/-- Number of `l`-tuples `x` with `r + Σ_j w (x j) ≡ 0 mod m`. With `β = Fin ρ × Fin ρ`,
`w (u, v) = 2^(u+1) - 2^(v+1)` and `r = 0` it is Hathi's `N_l(d)` of display 2.7. -/
def cntF {β : Type*} [Fintype β] (l : ℕ) (m : ℤ) (w : β → ℤ) (r : ℤ) : ℕ :=
  (univ.filter (fun x : Fin l → β => (r + ∑ j, w (x j)) % m = 0)).card

theorem cntF_succ {β : Type*} [Fintype β] (l : ℕ) (m : ℤ) (w : β → ℤ) (r : ℤ) :
    cntF (l + 1) m w r = ∑ b, cntF l m w (r + w b) := by
  classical
  unfold cntF
  simp only [card_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (l + 1) => β)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun x _ => ?_))
  simp [Fin.sum_univ_succ, add_assoc]

theorem cntF_emod {β : Type*} [Fintype β] (l : ℕ) (m : ℤ) (w : β → ℤ) (r : ℤ) :
    cntF l m w (r % m) = cntF l m w r := by
  unfold cntF
  congr 1
  ext x
  simp [Int.emod_add_emod]

/-- Memo table: entry `i < m` holds the count for residue `i`. -/
def tab {β : Type*} [Fintype β] (m : ℕ) (w : β → ℤ) : ℕ → List ℕ
  | 0 => (List.range m).map (fun i : ℕ => if i = 0 then 1 else 0)
  | l + 1 => (List.range m).map
      (fun i : ℕ => ∑ b, (tab m w l).getD ((((i : ℤ) + w b) % (m : ℤ)).toNat) 0)

theorem getD_map_range (m i : ℕ) (f : ℕ → ℕ) (h : i < m) :
    ((List.range m).map f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range h]

theorem emod_toNat_lt (r : ℤ) (m : ℕ) (hm : 0 < m) : (r % (m : ℤ)).toNat < m := by
  have h1 : 0 ≤ r % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have h2 : r % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  omega

theorem cntF_eq_tab {β : Type*} [Fintype β] (m : ℕ) (hm : 0 < m) (w : β → ℤ) :
    ∀ l (r : ℤ), cntF l (m : ℤ) w r = (tab m w l).getD ((r % (m : ℤ)).toNat) 0 := by
  intro l
  induction l with
  | zero =>
    intro r
    rw [tab, getD_map_range _ _ _ (emod_toNat_lt r m hm)]
    unfold cntF
    have h0 : 0 ≤ r % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
    by_cases h : r % (m : ℤ) = 0
    · have : (r % (m : ℤ)).toNat = 0 := by omega
      simp [h]
    · have : (r % (m : ℤ)).toNat ≠ 0 := by omega
      simp [h]
      omega
  | succ l ih =>
    intro r
    rw [cntF_succ, tab, getD_map_range _ _ _ (emod_toNat_lt r m hm)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ih]
    have h0 : 0 ≤ r % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
    have : (((r % (m : ℤ)).toNat : ℕ) : ℤ) = r % (m : ℤ) := Int.toNat_of_nonneg h0
    rw [this, Int.emod_add_emod]

/-- Hathi's weight `2^u - 2^v` with `1 ≤ u, v ≤ ρ`, `u = i + 1`. -/
def wt (ρ : ℕ) (b : Fin ρ × Fin ρ) : ℤ := 2 ^ (b.1.val + 1) - 2 ^ (b.2.val + 1)

/-- `ρ(15) = 4`, `ρ(3) = 2`. -/
theorem rho15 : 2 ^ 4 % 15 = 1 ∧ ∀ k, 0 < k → k < 4 → 2 ^ k % 15 ≠ 1 := by
  refine ⟨by norm_num, fun k h1 h2 => ?_⟩
  interval_cases k <;> norm_num
theorem rho3 : 2 ^ 2 % 3 = 1 ∧ 2 ^ 1 % 3 ≠ 1 := by norm_num

theorem tab15 : (tab 15 (wt 4) 5).getD 0 0 = 70588 := by decide +kernel
theorem tab3 : (tab 3 (wt 2) 5).getD 0 0 = 342 := by decide +kernel

/-- `N_5(15) = 70588`, Hathi 2.7 with `d = 15`, `ρ = 4`, `l = 5`. -/
theorem N5_15 : cntF 5 15 (wt 4) 0 = 70588 := by
  have h := cntF_eq_tab 15 (by norm_num) (wt 4) 5 0
  simp only [Nat.cast_ofNat] at h
  exact h.trans tab15

/-- `N_5(3) = 342`, Hathi 2.7 with `d = 3`, `ρ = 2`, `l = 5`. -/
theorem N5_3 : cntF 5 3 (wt 2) 0 = 342 := by
  have h := cntF_eq_tab 3 (by norm_num) (wt 2) 5 0
  simp only [Nat.cast_ofNat] at h
  exact h.trans tab3

/-- The `d = 1` terms of 2.10 at `l = 5`: `75/32 · N₅(3)/2¹⁰ + 105/32 · N₅(15)/4¹⁰`. -/
theorem d1_terms :
    (75 / 32 : ℚ) * ((cntF 5 3 (wt 2) 0 : ℚ) / 2 ^ 10) +
      105 / 32 * ((cntF 5 15 (wt 4) 0 : ℚ) / 4 ^ 10) = 8419335 / 8388608 := by
  rw [N5_3, N5_15]; norm_num

/-- Hathi's `c_{0,5}` of 2.10, for any nonnegative summable `f, g` standing for the terms
`μ²(d)/(c(d) β₅(3d))` and `μ²(d)/(c(d) β₅(15d))`, with the `d = 1` terms from 2.7, 2.8. -/
theorem hathi_c05_ge (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ d, 0 ≤ f d) (hg0 : ∀ d, 0 ≤ g d)
    (hf1 : f 1 = (cntF 5 3 (wt 2) 0 : ℝ) / 2 ^ 10)
    (hg1 : g 1 = (cntF 5 15 (wt 4) 0 : ℝ) / 4 ^ 10) :
    (8419335 / 8388608 : ℝ) ≤ 75 / 32 * (∑' d, f d) + 105 / 32 * (∑' d, g d) := by
  have a := hf.le_tsum 1 (fun j _ => hf0 j)
  have b := hg.le_tsum 1 (fun j _ => hg0 j)
  rw [hf1, N5_3] at a
  rw [hg1, N5_15] at b
  norm_num at a b
  nlinarith

theorem printed_lt : (7773 / 10000 : ℝ) < 8419335 / 8388608 := by norm_num

/-- `λ₀ = 0.8844473`. -/
def lam0 : ℚ := 8844473 / 10000000

/-- Section 4 criterion `0.9 - λ₀^{k'-10} · 11 · c > 0` at `l = 5` fails at `k' = 30` for
every `c ≥ 0.9537`; the Python lower bound for the true sum is `0.9696`. -/
theorem k30_fails_of (c : ℚ) (hc : 9537 / 10000 ≤ c) :
    9 / 10 - lam0 ^ (30 - 2 * 5) * 11 * c < 0 := by
  have h : 9 / 10 - lam0 ^ (30 - 2 * 5) * 11 * (9537 / 10000) < 0 := by
    unfold lam0; norm_num
  have : 0 ≤ lam0 ^ (30 - 2 * 5) * 11 := by unfold lam0; positivity
  nlinarith [mul_le_mul_of_nonneg_left hc this]

/-- It holds at `k' = 31` for every `0 ≤ c ≤ 1.07`. -/
theorem k31_ok_of (c : ℚ) (hc : c ≤ 107 / 100) :
    0 < 9 / 10 - lam0 ^ (31 - 2 * 5) * 11 * c := by
  have h : 0 < 9 / 10 - lam0 ^ (31 - 2 * 5) * 11 * (107 / 100) := by
    unfold lam0; norm_num
  have : 0 ≤ lam0 ^ (31 - 2 * 5) * 11 := by unfold lam0; positivity
  nlinarith [mul_le_mul_of_nonneg_left hc this]

/-- Local factor at `p = 5` when `5 ∣ h`, from the table `B(5, h) = (p-1)(p²+6p+1)` of
Hathi page 5, P0101 page 196, P0102 page 88: `1 + 224/256 = 15/8 ≠ 3/2`. -/
theorem factor5_dvd :
    (1 : ℚ) + ((5 - 1) * (5 ^ 2 + 6 * 5 + 1)) / (5 - 1) ^ 4 = 15 / 8 ∧ (15 / 8 : ℚ) ≠ 3 / 2 := by
  norm_num

end LeanLab.Hathi2021.FalsifierU6830
