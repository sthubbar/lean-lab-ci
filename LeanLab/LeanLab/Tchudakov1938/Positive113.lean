/- AI-written Lean code by OpenAI Codex, task113, 2026-10-26. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Euler113
namespace LeanLab.Tchudakov1938.Positive113
open Finset
open LeanLab.Tchudakov1938.Euler113
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Finset
/-- LEAF. P0064, page 29, inequality 3, finite telescoping product. -/
theorem telescoping_product (N : ℕ) :
    (∏ n ∈ Icc 2 (N + 2), (1 - 1 / (n : ℝ)^2)) = (N + 3 : ℕ) / (2 * ((N + 2 : ℕ) : ℝ)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [show N.succ + 2 = (N + 2) + 1 by omega, prod_Icc_succ_top (by omega), ih]
    push_cast
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    ring

/-- LEAF. P0064, page 29, inequality 3. Any finite subproduct with indices at least two is at least one half. -/
theorem product_lower (s : Finset ℕ) (hs : ∀ n ∈ s, 2 ≤ n) :
    (1 / 2 : ℝ) ≤ ∏ n ∈ s, (1 - 1 / (n : ℝ)^2) := by
  let N := s.sup id
  have hsub : s ⊆ Icc 2 (N + 2) := by
    intro n hn
    exact mem_Icc.mpr ⟨hs n hn, (Finset.le_sup (f := id) hn).trans (by omega)⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hsub
    (f := fun n : ℕ => (1 - 1 / (n : ℝ)^2))
    (fun n hn => by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith)
    (fun n hn _ => sub_le_self _ (by positivity))
  rw [telescoping_product N] at hprod
  apply le_trans ?_ hprod
  rw [le_div_iff₀ (by positivity)]
  push_cast
  linarith

/-- P0064, page 29, real Euler local factor in the printed two-product identity. -/
noncomputable def realFactor (m : ℕ) (p : Nat.Primes) : ℝ :=
  if p.val ∣ m then 1 + 1 / ((p.val : ℝ) - 1) else 1 - 1 / ((p.val : ℝ) - 1)^2

/-- LEAF. P0064, page 29, inequality 3. Finite prime products for even m are at least one half. -/
theorem finite_factor_lower (m : ℕ) (hm : Even m) (s : Finset Nat.Primes) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ s, realFactor m p := by
  classical
  let t := s.filter (fun p => ¬ p.val ∣ m)
  have hodd (p : Nat.Primes) (hp : p ∈ t) : 3 ≤ p.val := by
    have hnot := (mem_filter.mp hp).2
    have he : 2 ∣ m := even_iff_two_dvd.mp hm
    have h2 := p.property.two_le
    by_contra hh
    have : p.val = 2 := by omega
    exact hnot (this ▸ he)
  have ht (p : Nat.Primes) (hp : p ∈ t) : 2 ≤ p.val - 1 := by have := hodd p hp; omega
  have hi : Set.InjOn (fun p : Nat.Primes => p.val - 1) (t : Set Nat.Primes) := by
    intro p hp q hq h
    apply Subtype.ext
    change p.val - 1 = q.val - 1 at h
    have := hodd p hp
    have := hodd q hq
    omega
  have H := product_lower (t.image (fun p => p.val - 1)) (by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact ht p hp)
  rw [prod_image hi] at H
  have htf : (∏ p ∈ t, (1 - 1 / ((p.val - 1 : ℕ) : ℝ)^2)) = ∏ p ∈ t, realFactor m p := by
    apply prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p.val := p.property.one_le
    simp only [realFactor, ite_eq_right (mem_filter.mp hp).2, Nat.cast_sub hp1, Nat.cast_one]
  rw [htf] at H
  apply H.trans
  apply prod_le_prod_of_subset_of_one_le₀ (filter_subset _ _)
  · intro p hp
    have hp3 := hodd p hp
    rw [realFactor, ite_eq_right (mem_filter.mp hp).2, sub_nonneg, div_le_one (by
      have : (3 : ℝ) ≤ p.val := by exact_mod_cast hp3
      exact sq_pos_of_pos (by linarith))]
    have : (3 : ℝ) ≤ p.val := by exact_mod_cast hp3
    nlinarith
  · intro p hp hpt
    have hd : p.val ∣ m := by simpa [t, mem_filter, hp] using hpt
    rw [realFactor, ite_eq_left hd]
    have hp2 : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.two_le
    have : 0 ≤ 1 / ((p.val : ℝ) - 1) := (one_div_pos.mpr (by linarith)).le
    linarith

/-- LEAF. P0064, page 29, identify the real local factor with one plus A_m of p. -/
theorem local_eq_complex (m : ℕ) (p : Nat.Primes) :
    1 + coefficientNat m p.val = (realFactor m p : ℂ) := by
  rw [coefficientNat, dite_eq_right p.property.ne_zero,
    LeanLab.Tchudakov1938.PrimeValues113.coefficient_prime ⟨p.val, p.property.pos⟩ p.property m]
  simp only [PNat.mk_coe]
  unfold realFactor
  split_ifs <;> push_cast <;> ring


/-- P0064, page 29, inequality 3. The full singular series has real part at least one half for positive even m. -/
theorem singular_series_lower (m : ℕ) (hm : 0 < m) (heven : Even m) :
    (1 / 2 : ℝ) ≤ (∑' q : ℕ+, LeanLab.Tchudakov1938.Decomp113.coefficient m q).re := by
  rw [tsum_positive_eq_nat m hm]
  have H : Filter.Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, (1 + coefficientNat m p.val))
      Filter.atTop (nhds (∑' q : ℕ, coefficientNat m q)) := hasProd_local m hm
  have hr := (Complex.continuous_re.tendsto (∑' q : ℕ, coefficientNat m q)).comp H
  apply ge_of_tendsto hr
  apply Filter.Eventually.of_forall
  intro s
  simp only [Function.comp_apply]
  simp_rw [local_eq_complex]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]
  exact finite_factor_lower m heven s

/-- CITED. P0064, Lemma 4 part 3, pages 28 and 29.
The complex encoding of the real singular series uses its real part. -/
def lemma4PositiveStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m → Even m →
    c ≤ (∑' q : ℕ+, LeanLab.Tchudakov1938.Decomp113.coefficient m q).re

/-- P0064, Lemma 4 part 3, exact cited proposition assembled with c equal to one half. -/
theorem lemma4_positive : lemma4PositiveStatement := by
  exact ⟨1 / 2, by norm_num, singular_series_lower⟩

end LeanLab.Tchudakov1938.Positive113
