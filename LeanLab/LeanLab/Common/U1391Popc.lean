/-
A certified bignum popcount for the Lean kernel, unit U-1391, PC run 20261021T1003Z-20044.
Track T1, ladder rung 5b shared inputs. AI-written Lean code, Claude, 2026-10-21.
Checked only by the Lean kernel. Known technique: the SWAR popcount, Hacker's Delight 5-1,
run on whole natural numbers, so each level is a handful of GMP operations.

`popc K y` adds the bits of `y` below `2^K` in `K` levels: at level `k` the number holds
`2^(K-k)` fields of width `2^k`, each field the number of set bits of `y` in its range, and one
level adds neighbouring fields, `(y &&& M) + ((y >>> W) &&& M)` with the mask `M` that keeps the
low half of every block of width `2W`. No carry can cross a field, since two counts below `2^W`
add to less than `2^(2W)`.

`popc_eq` : `popc K y = #{i ∈ range (2^K) | y.testBit i}`. No cited input.
-/
import Mathlib

namespace LeanLab.Common.U1391

open Finset

/-- The `j`-th digit of `y` in base `2^W`. -/
def dg (W y j : ℕ) : ℕ := (y >>> (W * j)) % 2 ^ W

/-- The digit sum of the first `m` digits of `y` in base `2^W`. -/
def S (W m y : ℕ) : ℕ := ∑ j ∈ range m, dg W y j

/-- The mask with digit `2^W - 1` in each of the first `m` digits of base `2^(2W)`. -/
def mask (W m : ℕ) : ℕ := (2 ^ W - 1) * ((2 ^ (2 * W * m) - 1) / (2 ^ (2 * W) - 1))

/-- One SWAR level. -/
def step (W m y : ℕ) : ℕ := (y &&& mask W m) + ((y >>> W) &&& mask W m)

/-- `l` SWAR levels starting from field width `W`. -/
def pcA : ℕ → ℕ → ℕ → ℕ
  | W, 0, y => y % 2 ^ W
  | W, l + 1, y => pcA (2 * W) l (step W (2 ^ l) y)

/-- The number of set bits of `y` below `2^K`. -/
def popc (K y : ℕ) : ℕ := pcA 1 K y

lemma sum_succ_shift (W m : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ range (m + 1), f j * 2 ^ (W * j) = f 0 + 2 ^ W * ∑ j ∈ range m, f (j + 1) * 2 ^ (W * j) := by
  rw [sum_range_succ', mul_sum]
  simp only [mul_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [mul_add, mul_one, pow_add]
  ring

/-- Uniqueness of base `2^W` digits. -/
theorem uniq (W : ℕ) : ∀ (m : ℕ) (v : ℕ → ℕ), (∀ j < m, v j < 2 ^ W) →
    (∀ j < m, dg W (∑ i ∈ range m, v i * 2 ^ (W * i)) j = v j) ∧
      ∑ i ∈ range m, v i * 2 ^ (W * i) < 2 ^ (W * m)
  | 0, v, _ => by simp
  | m + 1, v, hv => by
    obtain ⟨ih1, ih2⟩ := uniq W m (fun j => v (j + 1)) (fun j hj => hv (j + 1) (by omega))
    rw [sum_succ_shift]
    set y' := ∑ j ∈ range m, v (j + 1) * 2 ^ (W * j) with hy'
    have h0 := hv 0 (by omega)
    have hp : 0 < 2 ^ W := by positivity
    have hdiv : (v 0 + 2 ^ W * y') / 2 ^ W = y' := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h0, zero_add]
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases j with _ | j
      · simp only [dg, mul_zero, Nat.shiftRight_zero]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
      · have := ih1 j (by omega)
        simp only [dg] at this ⊢
        have hs : (v 0 + 2 ^ W * y') >>> W = y' := by rw [Nat.shiftRight_eq_div_pow]; exact hdiv
        rw [show W * (j + 1) = W + W * j by ring, Nat.shiftRight_add, hs]
        exact this
    · rw [show W * (m + 1) = W + W * m by ring, pow_add]
      have : y' + 1 ≤ 2 ^ (W * m) := ih2
      nlinarith

/-- Base `2^W` representation. -/
theorem repr (W : ℕ) : ∀ (m y : ℕ), y < 2 ^ (W * m) → y = ∑ j ∈ range m, dg W y j * 2 ^ (W * j)
  | 0, y, h => by simp at h; simp [h]
  | m + 1, y, h => by
    have hp : 0 < 2 ^ W := by positivity
    have hq : y / 2 ^ W < 2 ^ (W * m) := by
      rw [Nat.div_lt_iff_lt_mul hp, ← pow_add]; rw [show W * m + W = W * (m + 1) by ring]; exact h
    have ih := repr W m (y / 2 ^ W) hq
    rw [sum_succ_shift]
    have e0 : dg W y 0 = y % 2 ^ W := by simp [dg]
    have e1 : ∀ j, dg W y (j + 1) = dg W (y / 2 ^ W) j := by
      intro j
      simp only [dg]
      rw [show W * (j + 1) = W + W * j by ring, Nat.shiftRight_add,
        show y >>> W = y / 2 ^ W from Nat.shiftRight_eq_div_pow y W]
    simp only [e0, e1]
    rw [← ih]
    exact (Nat.mod_add_div y (2 ^ W)).symm

lemma geom (B m : ℕ) : (B - 1) * ((B ^ m - 1) / (B - 1)) = B ^ m - 1 := by
  have h : B - 1 ∣ B ^ m - 1 := by exact Nat.sub_one_dvd_pow_sub_one B m
  exact Nat.mul_div_cancel' h

lemma mask_eq (W m : ℕ) (hW : 1 ≤ W) :
    mask W m = ∑ j ∈ range m, (2 ^ W - 1) * 2 ^ (2 * W * j) := by
  have hB : 2 ≤ 2 ^ (2 * W) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs : ∑ j ∈ range m, (2 ^ (2 * W)) ^ j = ((2 ^ (2 * W)) ^ m - 1) / (2 ^ (2 * W) - 1) :=
    Nat.geomSum_eq hB m
  unfold mask
  rw [← mul_sum]
  congr 1
  rw [pow_mul, ← hs]
  apply sum_congr rfl
  intro j _
  rw [← pow_mul]

lemma dg_and (W y M j : ℕ) : dg W (y &&& M) j = dg W y j &&& dg W M j := by
  simp only [dg]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_shiftRight]
  cases decide (i < W) <;> simp

lemma dg_mask (W m j : ℕ) (hW : 1 ≤ W) (hj : j < m) : dg (2 * W) (mask W m) j = 2 ^ W - 1 := by
  rw [mask_eq W m hW]
  have hlt : 2 ^ W - 1 < 2 ^ (2 * W) := by
    have : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 0 < 2 ^ W := by positivity
    omega
  have := (uniq (2 * W) m (fun _ => 2 ^ W - 1) (fun _ _ => hlt)).1 j hj
  simpa [mul_comm] using this

lemma mask_lt (W m : ℕ) (hW : 1 ≤ W) : mask W m < 2 ^ (2 * W * m) := by
  rw [mask_eq W m hW]
  have hlt : 2 ^ W - 1 < 2 ^ (2 * W) := by
    have : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 0 < 2 ^ W := by positivity
    omega
  have := (uniq (2 * W) m (fun _ => 2 ^ W - 1) (fun _ _ => hlt)).2
  simpa [mul_comm] using this

lemma dg_and_mask (W m y j : ℕ) (hW : 1 ≤ W) (hj : j < m) :
    dg (2 * W) (y &&& mask W m) j = dg W y (2 * j) := by
  rw [dg_and, dg_mask W m j hW hj, Nat.and_two_pow_sub_one_eq_mod]
  simp only [dg]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  ring_nf

lemma dg_shift (W y j : ℕ) : dg W (y >>> W) j = dg W y (j + 1) := by
  simp only [dg]
  rw [← Nat.shiftRight_add]
  congr 2
  ring

lemma sum_even_odd (f : ℕ → ℕ) : ∀ m : ℕ,
    ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) = ∑ i ∈ range (2 * m) , f i
  | 0 => by simp
  | m + 1 => by
    rw [sum_range_succ, sum_even_odd f m, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      sum_range_succ, sum_range_succ]
    ring

/-- **One SWAR level halves the number of fields and keeps the digit sum.** -/
theorem S_step (W m y : ℕ) (hW : 1 ≤ W) : S (2 * W) m (step W m y) = S W (2 * m) y := by
  set M := mask W m
  set u := y &&& M
  set v := (y >>> W) &&& M
  have hMl := mask_lt W m hW
  have hu : u < 2 ^ (2 * W * m) := lt_of_le_of_lt Nat.and_le_right hMl
  have hv : v < 2 ^ (2 * W * m) := lt_of_le_of_lt Nat.and_le_right hMl
  have ru := repr (2 * W) m u hu
  have rv := repr (2 * W) m v hv
  have du : ∀ j < m, dg (2 * W) u j = dg W y (2 * j) := fun j hj => dg_and_mask W m y j hW hj
  have dv : ∀ j < m, dg (2 * W) v j = dg W y (2 * j + 1) := fun j hj => by
    rw [dg_and_mask W m _ j hW hj, dg_shift]
  have hsum : u + v = ∑ j ∈ range m, (dg (2 * W) u j + dg (2 * W) v j) * 2 ^ (2 * W * j) := by
    conv_lhs => rw [ru, rv]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hbd : ∀ j < m, dg (2 * W) u j + dg (2 * W) v j < 2 ^ (2 * W) := by
    intro j hj
    rw [du j hj, dv j hj]
    have h1 : dg W y (2 * j) < 2 ^ W := Nat.mod_lt _ (by positivity)
    have h2 : dg W y (2 * j + 1) < 2 ^ W := Nat.mod_lt _ (by positivity)
    have : 2 ^ (2 * W) = 2 ^ W * 2 ^ W := by rw [← pow_add]; ring_nf
    have h3 : 2 ≤ 2 ^ W := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
    rw [this]; nlinarith
  have hd := (uniq (2 * W) m (fun j => dg (2 * W) u j + dg (2 * W) v j) hbd).1
  show ∑ j ∈ range m, dg (2 * W) (u + v) j = ∑ j ∈ range (2 * m), dg W y j
  rw [← sum_even_odd]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [hsum, hd j hj, du j hj, dv j hj]

theorem pcA_eq : ∀ (l W y : ℕ), 1 ≤ W → pcA W l y = S W (2 ^ l) y
  | 0, W, y, _ => by simp [pcA, S, dg]
  | l + 1, W, y, hW => by
    rw [pcA, pcA_eq l (2 * W) _ (by omega), S_step W _ y hW, pow_succ, mul_comm]

lemma dg_one (y i : ℕ) : dg 1 y i = if y.testBit i then 1 else 0 := by
  simp only [dg, one_mul, pow_one, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ i) with h | h <;> simp [h]

/-- **`popc K y` is the number of set bits of `y` below `2^K`.** -/
theorem popc_eq (K y : ℕ) : popc K y = #{i ∈ range (2 ^ K) | y.testBit i} := by
  rw [popc, pcA_eq K 1 y le_rfl, S, card_filter]
  exact sum_congr rfl fun i _ => dg_one y i

/-- Kernel test. -/
example : popc 4 0b1011011001 = 6 := by decide +kernel

end LeanLab.Common.U1391
