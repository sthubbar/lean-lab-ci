import Mathlib

/-!
# R-0048, T3 MOONSHOT: the sieve LP on A = {N - p} against the Liouville twisted example

Unit U-1465, PC run 20261022T0403Z-7595. AI wrote this Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Setting. A finite support `S`, a target set `P` of primes, true weights `a ≥ 0`, a `±1`
valued `lam` with `lam = -1` on `P`. The data are blocks `j ∈ J`; block `j` has rows
`m ∈ R j` with functionals `B j m`, and the constraint on a candidate `z` is
`∑_{m ∈ R j} |⟪B j m, z - a⟫| ≤ σ j`. A singleton block is an ordinary interval row, a
Type I row `d ∣ n`, or a Liouville class row; a block with many rows is the
Friedlander Iwaniec bilinear constraint, the sup over `|α_m| ≤ 1` of the bilinear form.

`lp_le_twisted`: every valid LP lower bound `β` for the prime mass satisfies
`β ≤ (1 - s) * ∑_P a` as soon as the twisted example `(1 + s lam) a` meets the data, and its
data defect is exactly `s` times the data of `lam * a`. For a Liouville row or a bilinear row
with `β = λ`, that defect is `s` times the class count, `class_shift` and `bilinear_shift`,
so a relative tolerance `eps` admits `s = eps`: `lp_fi_le`.
-/

namespace LeanLab.Routes.U1465

open Finset

/-- The twisted example bound. Unconditional. -/
theorem lp_le_twisted {α ι κ : Type*} [DecidableEq α] (S P : Finset α) (J : Finset ι)
    (R : ι → Finset κ) (B : ι → κ → α → ℝ) (σ : ι → ℝ) (lam a : α → ℝ) (β s : ℝ)
    (hβ : ∀ z : α → ℝ, (∀ n ∈ S, 0 ≤ z n) →
      (∀ j ∈ J, ∑ m ∈ R j, |∑ n ∈ S, B j m n * (z n - a n)| ≤ σ j) →
      β ≤ ∑ n ∈ S ∩ P, z n)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : ∀ n ∈ S, 0 ≤ a n)
    (hlam : ∀ n ∈ S, lam n = 1 ∨ lam n = -1) (hP : ∀ n ∈ S ∩ P, lam n = -1)
    (hfeas : ∀ j ∈ J, s * ∑ m ∈ R j, |∑ n ∈ S, B j m n * (lam n * a n)| ≤ σ j) :
    β ≤ (1 - s) * ∑ n ∈ S ∩ P, a n := by
  have key := hβ (fun n => (1 + s * lam n) * a n) ?_ ?_
  · calc β ≤ ∑ n ∈ S ∩ P, (1 + s * lam n) * a n := key
      _ = ∑ n ∈ S ∩ P, (1 - s) * a n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hP n hn]; ring
      _ = (1 - s) * ∑ n ∈ S ∩ P, a n := by rw [Finset.mul_sum]
  · intro n hn
    apply mul_nonneg _ (ha n hn)
    rcases hlam n hn with h | h <;> rw [h] <;> linarith
  · intro j hj
    calc ∑ m ∈ R j, |∑ n ∈ S, B j m n * ((1 + s * lam n) * a n - a n)|
        = ∑ m ∈ R j, s * |∑ n ∈ S, B j m n * (lam n * a n)| := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← abs_of_nonneg hs0, ← abs_mul, abs_of_nonneg hs0, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
      _ = s * ∑ m ∈ R j, |∑ n ∈ S, B j m n * (lam n * a n)| := by rw [Finset.mul_sum]
      _ ≤ σ j := hfeas j hj

/-- A Liouville class row `n ↦ [d ∣ n] lam n` evaluated on `lam * a` is the class count. -/
theorem class_shift (S : Finset ℕ) (lam a : ℕ → ℝ) (d : ℕ)
    (hlam : ∀ n ∈ S, lam n = 1 ∨ lam n = -1) :
    ∑ n ∈ S, (if d ∣ n then lam n else 0) * (lam n * a n)
      = ∑ n ∈ S.filter (fun n => d ∣ n), a n := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  split_ifs
  · rcases hlam n hn with h | h <;> rw [h] <;> ring
  · ring

/-- The real valued Liouville function, Mathlib's `ArithmeticFunction.liouville`. -/
noncomputable def lamR (n : ℕ) : ℝ := (ArithmeticFunction.liouville n : ℝ)

theorem lamR_pm {n : ℕ} (hn : n ≠ 0) : lamR n = 1 ∨ lamR n = -1 := by
  unfold lamR
  rw [ArithmeticFunction.liouville_apply hn]
  rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors n) with h | h <;> rw [h] <;> simp

theorem lamR_mul (m k : ℕ) : lamR (m * k) = lamR m * lamR k := by
  unfold lamR
  rw [ArithmeticFunction.liouville_apply_mul]; push_cast; ring

/-- A bilinear row with `β = λ`, `n ↦ [m ∣ n] λ (n / m)`, evaluated on `λ * a` is `λ m`
times the class count. So its absolute value is the class count. -/
theorem bilinear_shift (S : Finset ℕ) (a : ℕ → ℝ) (m : ℕ) (hS : ∀ n ∈ S, n ≠ 0) :
    ∑ n ∈ S, (if m ∣ n then lamR (n / m) else 0) * (lamR n * a n)
      = lamR m * ∑ n ∈ S.filter (fun n => m ∣ n), a n := by
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; exact hS _ hn (by simp)
    have hk : k ≠ 0 := by rintro rfl; exact hS _ hn (by simp)
    rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hm), lamR_mul]
    rcases lamR_pm hk with h | h <;> rw [h] <;> ring
  · ring

theorem abs_lamR_mul {m : ℕ} (hm : m ≠ 0) (x : ℝ) : |lamR m * x| = |x| := by
  rcases lamR_pm hm with h | h <;> rw [h] <;> simp

/-- Headline. The LP with Type I rows and Friedlander Iwaniec blocks with `β = λ`.
Type I rows `d ∈ Dset`: `|∑_{d ∣ n} (z n - a n)| ≤ τ d`. Bilinear blocks `j ∈ J`:
`∑_{m ∈ R j} |∑_{m ∣ n} λ(n/m) (z n - a n)| ≤ eps * ∑_{m ∈ R j} c_m`, `c_m` the class
count. If the Type I parity defects `E_d = ∑_{d ∣ n} λ n a n` satisfy `eps * |E_d| ≤ τ d`,
every valid lower bound is at most `(1 - eps)` times the true prime mass. Unconditional. -/
theorem lp_fi_le {ι : Type*} (S P : Finset ℕ) (Dset : Finset ℕ) (J : Finset ι)
    (R : ι → Finset ℕ) (τ : ℕ → ℝ) (a : ℕ → ℝ) (β eps : ℝ)
    (hS : ∀ n ∈ S, n ≠ 0) (hR : ∀ j ∈ J, ∀ m ∈ R j, m ≠ 0)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) (ha : ∀ n ∈ S, 0 ≤ a n)
    (hP : ∀ n ∈ S ∩ P, lamR n = -1)
    (hβ : ∀ z : ℕ → ℝ, (∀ n ∈ S, 0 ≤ z n) →
      (∀ d ∈ Dset, |∑ n ∈ S, (if d ∣ n then (1 : ℝ) else 0) * (z n - a n)| ≤ τ d) →
      (∀ j ∈ J, ∑ m ∈ R j, |∑ n ∈ S, (if m ∣ n then lamR (n / m) else 0) * (z n - a n)|
        ≤ eps * ∑ m ∈ R j, ∑ n ∈ S.filter (fun n => m ∣ n), a n) →
      β ≤ ∑ n ∈ S ∩ P, z n)
    (htypeI : ∀ d ∈ Dset, eps * |∑ n ∈ S.filter (fun n => d ∣ n), lamR n * a n| ≤ τ d) :
    β ≤ (1 - eps) * ∑ n ∈ S ∩ P, a n := by
  classical
  -- blocks: `Sum.inl d` is a Type I row, `Sum.inr j` a bilinear block
  let J' : Finset (ℕ ⊕ ι) := Dset.disjSum J
  let R' : ℕ ⊕ ι → Finset ℕ := fun x => Sum.elim (fun d => {d}) R x
  let B' : ℕ ⊕ ι → ℕ → ℕ → ℝ := fun x m n => Sum.elim
    (fun _ => if m ∣ n then (1 : ℝ) else 0) (fun _ => if m ∣ n then lamR (n / m) else 0) x
  let σ' : ℕ ⊕ ι → ℝ := fun x => Sum.elim τ
    (fun j => eps * ∑ m ∈ R j, ∑ n ∈ S.filter (fun n => m ∣ n), a n) x
  refine lp_le_twisted S P J' R' B' σ' lamR a β eps ?_ heps0 heps1 ha
    (fun n hn => lamR_pm (hS n hn)) hP ?_
  · intro z hz hblk
    refine hβ z hz (fun d hd => ?_) (fun j hj => ?_)
    · have := hblk (Sum.inl d) (Finset.inl_mem_disjSum.mpr hd)
      simpa [R', B', σ'] using this
    · exact hblk (Sum.inr j) (Finset.inr_mem_disjSum.mpr hj)
  · rintro (d | j) hx
    · have hd : d ∈ Dset := Finset.inl_mem_disjSum.mp hx
      have h := htypeI d hd
      simp only [R', B', σ', Sum.elim_inl, Finset.sum_singleton]
      rw [Finset.sum_filter] at h
      convert h using 3
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    · have hj : j ∈ J := Finset.inr_mem_disjSum.mp hx
      simp only [R', B', σ', Sum.elim_inr]
      gcongr with m hm
      rw [bilinear_shift S a m hS, abs_lamR_mul (hR j hj m hm)]
      exact (abs_of_nonneg (Finset.sum_nonneg fun n hn => ha n (Finset.mem_filter.mp hn).1)).le

/-- With exact parity balance on the Type I rows and full relative tolerance on the bilinear
blocks the bound is `0`: Selberg's parity example, here as a corollary. -/
theorem lp_fi_blind {ι : Type*} (S P : Finset ℕ) (Dset : Finset ℕ) (J : Finset ι)
    (R : ι → Finset ℕ) (τ : ℕ → ℝ) (a : ℕ → ℝ) (β : ℝ)
    (hS : ∀ n ∈ S, n ≠ 0) (hR : ∀ j ∈ J, ∀ m ∈ R j, m ≠ 0) (ha : ∀ n ∈ S, 0 ≤ a n)
    (hP : ∀ n ∈ S ∩ P, lamR n = -1)
    (hβ : ∀ z : ℕ → ℝ, (∀ n ∈ S, 0 ≤ z n) →
      (∀ d ∈ Dset, |∑ n ∈ S, (if d ∣ n then (1 : ℝ) else 0) * (z n - a n)| ≤ τ d) →
      (∀ j ∈ J, ∑ m ∈ R j, |∑ n ∈ S, (if m ∣ n then lamR (n / m) else 0) * (z n - a n)|
        ≤ 1 * ∑ m ∈ R j, ∑ n ∈ S.filter (fun n => m ∣ n), a n) →
      β ≤ ∑ n ∈ S ∩ P, z n)
    (htypeI : ∀ d ∈ Dset, |∑ n ∈ S.filter (fun n => d ∣ n), lamR n * a n| ≤ τ d) :
    β ≤ 0 := by
  have h := lp_fi_le S P Dset J R τ a β 1 hS hR zero_le_one le_rfl ha hP hβ
    (fun d hd => by rw [one_mul]; exact htypeI d hd)
  simpa using h

theorem lamR_prime {p : ℕ} (hp : p.Prime) : lamR p = -1 := by
  unfold lamR
  rw [ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]
  simp

/-- Vacuity for `lp_fi_le`: `S = {3, 4}`, `P = {3}`, `a = 1` on `S`, one Type I row `d = 1`
with `τ 1 = 1`, one bilinear block `R = {1, 2}`, `eps = 1/2`. The certificate `β = 0` is
valid, and the Type I defect `|λ 3 + λ 4| = 0` meets `htypeI`. -/
example : (0 : ℝ) ≤ (1 - 1 / 2) * ∑ _n ∈ ({3, 4} : Finset ℕ) ∩ {3}, (1 : ℝ) := by
  refine lp_fi_le ({3, 4} : Finset ℕ) {3} {1} ({0} : Finset ℕ) (fun _ => {1, 2})
    (fun _ => 1) (fun _ => 1) 0 (1 / 2) ?_ ?_ (by norm_num) (by norm_num) (fun _ _ => zero_le_one)
    ?_ ?_ ?_
  · intro n hn; simp at hn; omega
  · intro j _ m hm; simp at hm; omega
  · intro n hn
    have : n = 3 := by simp at hn; omega
    subst this; exact lamR_prime (by norm_num)
  · intro z hz _ _
    exact Finset.sum_nonneg fun n hn => hz n (Finset.mem_inter.mp hn).1
  · intro d hd
    have h4 : lamR 4 = 1 := by
      have : (4 : ℕ) = 2 * 2 := rfl
      rw [this, lamR_mul, lamR_prime (by norm_num)]; norm_num
    have hd1 : d = 1 := by simpa using hd
    subst hd1
    have : ({3, 4} : Finset ℕ).filter (fun n => 1 ∣ n) = {3, 4} := by decide
    rw [this, Finset.sum_pair (by norm_num), lamR_prime (by norm_num), h4]
    norm_num

end LeanLab.Routes.U1465
