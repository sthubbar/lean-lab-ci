/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the rough cofactor of display 5.15 the main term of that consequence is the
Buchstab identity for densities. This file proves its continuous half with integer levels:
the density `ω(log n / log z) / log z` of `n` at level `z` is the prime density `1 / log n`
plus the sum over levels `z ≤ k < n` of `ω(log (n / k) / log k) / (k log^2 k)`, up to
`O(1 / z)`, by telescoping the level and the delay equation `(u ω(u))' = ω(u - 1)`;
`buchstab_telescope` is the summed form. Nothing is left open in this file.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.BuchstabIntegral517

namespace LeanLab.BHP1997.LowerShortC165
open Classical
open scoped BigOperators
open LeanLab.ChenDoubleSieve.Wu04Functional

/-- P0069 page 51, display 5.17, Buchstab function input: the second order form of the delay
equation `(u ω(u))' = ω(u - 1)`. For `2 ≤ u1 ≤ u2` the increment of `u ω(u)` is
`(u2 - u1) ω(u2 - 1)` up to `(u2 - u1)^2`, by the mean value theorem and the Lipschitz bound. -/
theorem psi_second_order {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {u1 u2 : ℝ} (h1 : 2 ≤ u1) (h12 : u1 ≤ u2) :
    |u2 * ω u2 - u1 * ω u1 - (u2 - u1) * ω (u2 - 1)| ≤ (u2 - u1) ^ 2 := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · simp
  have hc : ContinuousOn (fun w : ℝ => w * ω w) (Set.Icc u1 u2) :=
    continuousOn_id.mul (hω.1.mono fun w hw => by
      simp only [Set.mem_Ici]
      linarith [hw.1])
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun w : ℝ => w * ω w)
    (fun w => ω (w - 1)) hlt hc (fun w hw => hω.2.2 w (by linarith [hw.1]))
  have hpos : 0 < u2 - u1 := sub_pos.mpr hlt
  have he : u2 * ω u2 - u1 * ω u1 = (u2 - u1) * ω (ξ - 1) := by
    rw [hξe]
    field_simp
  have hl := Decomp514a.two_density_buchstab_lipschitz hω hz (u := ξ - 1) (v := u2 - 1)
    (by linarith [hξ.1]) (by linarith [hξ.2])
  rw [he, ← mul_sub, abs_mul, abs_of_pos hpos, sq]
  apply mul_le_mul_of_nonneg_left _ hpos.le
  linarith [hξ.1]

/-- P0069 page 51, display 5.17, Buchstab function input: across `u = 2`, where `u ω(u)` leaves
the constant `1`, the increment of `u ω(u)` is at most first order. -/
theorem psi_kink {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {u1 u2 : ℝ} (h1 : 1 ≤ u1) (h1' : u1 ≤ 2) (h2 : 2 ≤ u2) :
    |u2 * ω u2 - u1 * ω u1| ≤ (u2 - u1) + (u2 - u1) ^ 2 := by
  have e1 : u1 * ω u1 = 1 := by
    rw [hω.2.1 u1 h1 h1']
    field_simp
  have e2 : (2 : ℝ) * ω 2 = 1 := by
    rw [hω.2.1 2 (by norm_num) le_rfl]
    norm_num
  have h := psi_second_order hω hz (le_refl 2) h2
  obtain ⟨hb1, hb2⟩ := buchstab_bounds hω (u := u2 - 1) (by linarith)
  obtain ⟨ha, hb⟩ := abs_le.mp h
  rw [e2] at ha hb
  rw [e1, abs_le]
  have hsq : (u2 - 2) ^ 2 ≤ (u2 - u1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hm1 : (u2 - 2) * ω (u2 - 1) ≤ (u2 - 2) * 1 :=
    mul_le_mul_of_nonneg_left hb2 (by linarith)
  have hm2 : 0 ≤ (u2 - 2) * ω (u2 - 1) := mul_nonneg (by linarith) (by linarith)
  have hs0 : 0 ≤ (u2 - u1) ^ 2 := sq_nonneg _
  constructor <;> linarith

/-- P0069 page 51, display 5.17: size of the squared increment `U = u2 - u1` of
`u = log n / log k` over one step of the level `k`, in logarithmic variables. -/
theorem U_sq_le {M κ l l' L U : ℝ} (hκ : 1 ≤ κ) (hl : 1 ≤ l) (hll : l ≤ l')
    (hδ1 : l' - l ≤ 1 / κ) (hL0 : 0 < L)
    (hLM : L ≤ M * l) (hU : U = L * (l' - l) / (l * l')) : U ^ 2 ≤ M / κ ^ 2 * L := by
  have hκ0 : 0 < κ := by linarith
  have hl0 : 0 < l := by linarith
  have hl'0 : 0 < l' := by linarith
  have hδ0 : 0 ≤ l' - l := by linarith
  have hM0 : 0 ≤ M := by nlinarith
  have hMκ : 0 ≤ M / κ ^ 2 := div_nonneg hM0 (by positivity)
  have hδsq : (l' - l) ^ 2 ≤ 1 / κ ^ 2 := by
    have := pow_le_pow_left₀ hδ0 hδ1 2
    simpa [div_pow] using this
  have hprod : 1 ≤ l * l' := by nlinarith
  have hll2 : l ≤ (l * l') ^ 2 := by nlinarith
  have hU2 : U ^ 2 = L * (L * (l' - l) ^ 2 / (l * l') ^ 2) := by
    rw [hU]
    field_simp
  have h3 : L * (l' - l) ^ 2 ≤ M / κ ^ 2 * (l * l') ^ 2 := by
    calc L * (l' - l) ^ 2 ≤ (M * l) * (1 / κ ^ 2) :=
          mul_le_mul hLM hδsq (sq_nonneg _) (by positivity)
      _ = M / κ ^ 2 * l := by ring
      _ ≤ M / κ ^ 2 * (l * l') ^ 2 := mul_le_mul_of_nonneg_left hll2 hMκ
  have h4 : L * (l' - l) ^ 2 / (l * l') ^ 2 ≤ M / κ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    exact h3
  calc U ^ 2 = (L * (l' - l) ^ 2 / (l * l') ^ 2) * L := by rw [hU2]; ring
    _ ≤ M / κ ^ 2 * L := mul_le_mul_of_nonneg_right h4 hL0.le

/-- P0069 page 51, display 5.17: the real inequality behind one step in the least prime factor
variable, from level `k` to level `k + 1`, in the logarithmic variables `l = log k`,
`l' = log (k + 1)`, `L = log n`. -/
theorem step_real_bound {M κ l l' L d w U : ℝ} (hκ : 1 ≤ κ) (hl : 1 ≤ l) (hll : l ≤ l')
    (hδ1 : l' - l ≤ 1 / κ) (hδ2 : 1 / κ - 1 / κ ^ 2 ≤ l' - l) (hL0 : 0 < L)
    (hLM : L ≤ M * l) (hw : |w| ≤ 1) (hU : U = L * (l' - l) / (l * l'))
    (hD : |L * d - U * w| ≤ U ^ 2) : |d - w / (κ * l ^ 2)| ≤ (M + 2) / κ ^ 2 := by
  have hκ0 : 0 < κ := by linarith
  have hl0 : 0 < l := by linarith
  have hl'0 : 0 < l' := by linarith
  have hl'1 : 1 ≤ l' := by linarith
  have hδ0 : 0 ≤ l' - l := by linarith
  have hM0 : 0 ≤ M := by nlinarith
  have hMκ : 0 ≤ M / κ ^ 2 := div_nonneg hM0 (by positivity)
  have e : d - w / (κ * l ^ 2) =
      (L * d - U * w) / L + w * ((l' - l) / (l * l') - 1 / (κ * l ^ 2)) := by
    rw [hU]
    field_simp
    ring
  have hδsq : (l' - l) ^ 2 ≤ 1 / κ ^ 2 := by
    have := pow_le_pow_left₀ hδ0 hδ1 2
    simpa [div_pow] using this
  have hprod : 1 ≤ l * l' := by nlinarith
  have hll2 : l ≤ (l * l') ^ 2 := by nlinarith
  have hUsq := U_sq_le hκ hl hll hδ1 hL0 hLM hU
  have t1 : |(L * d - U * w) / L| ≤ M / κ ^ 2 := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    exact hD.trans hUsq
  have t2 : |(l' - l) / (l * l') - 1 / (κ * l ^ 2)| ≤ 2 / κ ^ 2 := by
    have key : 1 / (κ * l ^ 2) - (l' - l) / (l * l') =
        (l' - κ * (l' - l) * l) / (κ * l ^ 2 * l') := by
      field_simp
    have hκδ : 1 - κ * (l' - l) ≤ 1 / κ := by
      have := mul_le_mul_of_nonneg_left hδ2 hκ0.le
      have e3 : κ * (1 / κ - 1 / κ ^ 2) = 1 - 1 / κ := by
        field_simp
      linarith
    have hnum : l' - κ * (l' - l) * l ≤ 2 * l / κ := by
      have h5 := mul_le_mul_of_nonneg_left hκδ hl0.le
      have e5 : l * (1 / κ) = l / κ := by ring
      have h6 : 1 / κ ≤ l / κ := div_le_div_of_nonneg_right hl hκ0.le
      have e6 : 2 * l / κ = l / κ + l / κ := by ring
      nlinarith
    have hup : (l' - l) / (l * l') ≤ 1 / (κ * l ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h7 : (l' - l) * κ ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hδ1 hκ0.le
        have e7 : 1 / κ * κ = 1 := by field_simp
        linarith
      have h8 : l ^ 2 ≤ l * l' := by nlinarith
      calc (l' - l) * (κ * l ^ 2) = ((l' - l) * κ) * l ^ 2 := by ring
        _ ≤ 1 * l ^ 2 := mul_le_mul_of_nonneg_right h7 (sq_nonneg _)
        _ ≤ 1 * (l * l') := by linarith
    have hlow : 1 / (κ * l ^ 2) - (l' - l) / (l * l') ≤ 2 / κ ^ 2 := by
      rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
      have h9 : (l' - κ * (l' - l) * l) * κ ≤ 2 * l := by
        have := mul_le_mul_of_nonneg_right hnum hκ0.le
        have e9 : 2 * l / κ * κ = 2 * l := by field_simp
        linarith
      have h10 : l ≤ l ^ 2 * l' := by nlinarith
      calc (l' - κ * (l' - l) * l) * κ ^ 2 = ((l' - κ * (l' - l) * l) * κ) * κ := by ring
        _ ≤ (2 * l) * κ := mul_le_mul_of_nonneg_right h9 hκ0.le
        _ ≤ 2 * (κ * l ^ 2 * l') := by nlinarith
    rw [abs_le]
    have : 0 ≤ 2 / κ ^ 2 := by positivity
    constructor <;> linarith
  have t3 : |w * ((l' - l) / (l * l') - 1 / (κ * l ^ 2))| ≤ 2 / κ ^ 2 := by
    rw [abs_mul]
    calc _ ≤ 1 * |(l' - l) / (l * l') - 1 / (κ * l ^ 2)| :=
          mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact t2
  rw [e]
  calc _ ≤ |(L * d - U * w) / L| + |w * ((l' - l) / (l * l') - 1 / (κ * l ^ 2))| :=
        abs_add_le _ _
    _ ≤ M / κ ^ 2 + 2 / κ ^ 2 := add_le_add t1 t3
    _ = _ := by ring

/-- P0069 page 51, display 5.17: the real inequality for the one step of the level `k` that
crosses `u = 2`, that is `k^2 ≤ n < (k + 1)^2`. -/
theorem kink_real_bound {M κ l l' L d w U : ℝ} (hκ : 1 ≤ κ) (hl : 1 ≤ l) (hll : l ≤ l')
    (hδ1 : l' - l ≤ 1 / κ) (hL0 : 0 < L)
    (hLM : L ≤ M * l) (hw : |w| ≤ 1) (hU : U = L * (l' - l) / (l * l'))
    (hD : |L * d| ≤ U + U ^ 2) : |d - w / (κ * l ^ 2)| ≤ (M + 2) / κ ^ 2 + 2 / κ := by
  have hκ0 : 0 < κ := by linarith
  have hl0 : 0 < l := by linarith
  have hl'0 : 0 < l' := by linarith
  have hδ0 : 0 ≤ l' - l := by linarith
  have hprod : 1 ≤ l * l' := by nlinarith
  have hUsq := U_sq_le hκ hl hll hδ1 hL0 hLM hU
  have hUL : U ≤ 1 / κ * L := by
    have h1 : (l' - l) / (l * l') ≤ 1 / κ := (div_le_self hδ0 hprod).trans hδ1
    calc U = (l' - l) / (l * l') * L := by rw [hU]; ring
      _ ≤ 1 / κ * L := mul_le_mul_of_nonneg_right h1 hL0.le
  have hd : |d| ≤ 1 / κ + M / κ ^ 2 := by
    rw [abs_mul, abs_of_pos hL0] at hD
    have h2 : L * |d| ≤ L * (1 / κ + M / κ ^ 2) := by linarith
    exact le_of_mul_le_mul_left h2 hL0
  have hw2 : |w / (κ * l ^ 2)| ≤ 1 / κ := by
    rw [abs_div, abs_of_pos (by positivity : 0 < κ * l ^ 2)]
    have h3 : κ ≤ κ * l ^ 2 := le_mul_of_one_le_right hκ0.le (by nlinarith)
    calc |w| / (κ * l ^ 2) ≤ 1 / (κ * l ^ 2) := div_le_div_of_nonneg_right hw (by positivity)
      _ ≤ 1 / κ := one_div_le_one_div_of_le hκ0 h3
  have h4 : 0 ≤ 2 / κ ^ 2 := by positivity
  calc _ ≤ |d| + |w / (κ * l ^ 2)| := abs_sub _ _
    _ ≤ (M + 2) / κ ^ 2 + 2 / κ := by
        have e : (M + 2) / κ ^ 2 = M / κ ^ 2 + 2 / κ ^ 2 := by ring
        have e2 : 2 / κ = 1 / κ + 1 / κ := by ring
        linarith

/-- P0069 page 51, display 5.17, the Buchstab identity in differential form. One step of the
level, from `k` to `k + 1`, changes the Buchstab density `ω(log n / log k) / log k` of `n` by
the density `ω(log (n / k) / log k) / (k log^2 k)` of the products `k m` near `n` with `m` free
of prime factors below `k`, up to `O(1 / k^2)`, apart from the one step with
`k^2 ≤ n < (k + 1)^2`. -/
theorem buchstab_step_error {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {M : ℝ} {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n)
    (hM : Real.log n ≤ M * Real.log k) :
    |ω (Real.log n / Real.log k) / Real.log k -
        ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ) -
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)| ≤
      (M + 2) / (k : ℝ) ^ 2 + (if k = Nat.sqrt n then 2 / (k : ℝ) else 0) := by
  have hκ3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ0 : (0 : ℝ) < k := by linarith
  have hκ1 : (1 : ℝ) ≤ k := by linarith
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl1 : 1 ≤ Real.log k :=
    (Real.le_log_iff_exp_le hκ0).mpr (by linarith [Real.exp_one_lt_d9])
  have hδ1 : Real.log ((k + 1 : ℕ) : ℝ) - Real.log k ≤ 1 / (k : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hk1 hκ0)
    rw [Real.log_div hk1.ne' hκ0.ne'] at h
    have e : ((k + 1 : ℕ) : ℝ) / k - 1 = 1 / (k : ℝ) := by
      push_cast
      field_simp
      ring
    linarith
  have hδ2 : 1 / (k : ℝ) - 1 / (k : ℝ) ^ 2 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log k := by
    have h := Real.log_le_sub_one_of_pos (div_pos hκ0 hk1)
    rw [Real.log_div hκ0.ne' hk1.ne'] at h
    have e : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -(1 / ((k : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    have e2 : 1 / (k : ℝ) - 1 / (k : ℝ) ^ 2 ≤ 1 / ((k : ℝ) + 1) := by
      rw [div_sub_div _ _ hκ0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hll : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_le_log hκ0 (by push_cast; linarith)
  have hl'L : Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log hk1 (by exact_mod_cast hkn)
  have hl0 : 0 < Real.log k := by linarith
  have hl'0 : 0 < Real.log ((k + 1 : ℕ) : ℝ) := by linarith
  have hL0 : 0 < Real.log n := by linarith
  have hM0 : 0 ≤ M := by nlinarith
  have hu1 : 1 ≤ Real.log n / Real.log ((k + 1 : ℕ) : ℝ) := (one_le_div hl'0).mpr hl'L
  have hu12 : Real.log n / Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log n / Real.log k :=
    div_le_div_of_nonneg_left hL0.le hl0 hll
  have hU : Real.log n / Real.log k - Real.log n / Real.log ((k + 1 : ℕ) : ℝ) =
      Real.log n * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) /
        (Real.log k * Real.log ((k + 1 : ℕ) : ℝ)) := by
    field_simp
  have hd : Real.log n * (ω (Real.log n / Real.log k) / Real.log k -
        ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ)) =
      Real.log n / Real.log k * ω (Real.log n / Real.log k) -
        Real.log n / Real.log ((k + 1 : ℕ) : ℝ) *
          ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) := by
    field_simp
  by_cases hA : (k + 1) ^ 2 ≤ n
  · have hne : k ≠ Nat.sqrt n := by
      intro h
      have := (Nat.eq_sqrt'.mp h).2
      omega
    rw [ite_eq_right hne, add_zero]
    have h2l : 2 * Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log n := by
      have := Real.log_le_log (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ 2)
        (by exact_mod_cast hA : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ n)
      rw [Real.log_pow] at this
      push_cast at this ⊢
      linarith
    have hu1' : 2 ≤ Real.log n / Real.log ((k + 1 : ℕ) : ℝ) := (le_div_iff₀ hl'0).mpr h2l
    have hD := psi_second_order hω hz hu1' hu12
    have hw : |ω (Real.log n / Real.log k - 1)| ≤ 1 := by
      obtain ⟨h1, h2⟩ := buchstab_bounds hω (u := Real.log n / Real.log k - 1) (by linarith)
      rw [abs_le]
      constructor <;> linarith
    rw [← hd] at hD
    exact step_real_bound hκ1 hl1 hll hδ1 hδ2 hL0 hM hw hU hD
  · by_cases hB : n < k ^ 2
    · have hne : k ≠ Nat.sqrt n := by
        intro h
        have := (Nat.eq_sqrt'.mp h).1
        omega
      rw [ite_eq_right hne, add_zero]
      have h2l : Real.log n < 2 * Real.log k := by
        have := Real.log_lt_log hn0 (by exact_mod_cast hB : (n : ℝ) < (k : ℝ) ^ 2)
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have hu2 : Real.log n / Real.log k < 2 := (div_lt_iff₀ hl0).mpr h2l
      have hu2' : 1 ≤ Real.log n / Real.log k := hu1.trans hu12
      have e1 := hω.2.1 _ hu2' hu2.le
      have e2 := hω.2.1 _ hu1 (hu12.trans hu2.le)
      have e3 := hz (Real.log n / Real.log k - 1) (by linarith)
      have hdz : ω (Real.log n / Real.log k) / Real.log k -
          ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ) = 0 := by
        rw [e1, e2]
        field_simp
        ring
      rw [hdz, e3]
      simp only [zero_div, sub_zero, abs_zero]
      positivity
    · have he : k = Nat.sqrt n := Nat.eq_sqrt'.mpr ⟨by omega, by omega⟩
      rw [ite_eq_left he]
      have h2l : 2 * Real.log k ≤ Real.log n := by
        have := Real.log_le_log (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)
          (by exact_mod_cast (by omega : k ^ 2 ≤ n) : (k : ℝ) ^ 2 ≤ n)
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have h2l' : Real.log n < 2 * Real.log ((k + 1 : ℕ) : ℝ) := by
        have := Real.log_lt_log hn0
          (by exact_mod_cast (by omega : n < (k + 1) ^ 2) : (n : ℝ) < ((k + 1 : ℕ) : ℝ) ^ 2)
        rw [Real.log_pow] at this
        push_cast at this ⊢
        linarith
      have hu2 : 2 ≤ Real.log n / Real.log k := (le_div_iff₀ hl0).mpr h2l
      have hu1' : Real.log n / Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 :=
        ((div_lt_iff₀ hl'0).mpr h2l').le
      have hD := psi_kink hω hz hu1 hu1' hu2
      have hw : |ω (Real.log n / Real.log k - 1)| ≤ 1 := by
        obtain ⟨h1, h2⟩ := buchstab_bounds hω (u := Real.log n / Real.log k - 1) (by linarith)
        rw [abs_le]
        constructor <;> linarith
      rw [← hd] at hD
      exact kink_real_bound hκ1 hl1 hll hδ1 hL0 hM hw hU hD

/-- P0069 page 51, display 5.17: the tail of `∑ 1 / k^2` from `z`, the total of the step errors
of `buchstab_step_error`. -/
theorem sum_inv_sq_Ico {z : ℕ} (hz : 2 ≤ z) (n : ℕ) (hzn : z ≤ n) :
    ∑ k ∈ Finset.Ico z n, 1 / (k : ℝ) ^ 2 ≤ 2 / (z : ℝ) := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have key : ∑ k ∈ Finset.Ico z n, 1 / (k : ℝ) ^ 2 ≤ 1 / ((z : ℝ) - 1) - 1 / ((n : ℝ) - 1) := by
    induction n, hzn using Nat.le_induction with
    | base => simp
    | succ n hzn ih =>
      rw [Finset.sum_Ico_succ_top hzn]
      have hn2 : (2 : ℝ) ≤ n := hz2.trans (by exact_mod_cast hzn)
      have hstep : 1 / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / (((n + 1 : ℕ) : ℝ) - 1) := by
        push_cast
        rw [add_sub_cancel_right, div_sub_div _ _ (by linarith) (by linarith),
          div_le_div_iff₀ (by positivity) (by nlinarith)]
        nlinarith
      linarith
  have hn1 : 0 ≤ 1 / ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ n := hz2.trans (by exact_mod_cast hzn)
    exact div_nonneg zero_le_one (by linarith)
  have h2 : 1 / ((z : ℝ) - 1) ≤ 2 / (z : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  linarith

/-- P0069 page 51, display 5.17, the Buchstab identity for the density of one integer `n ≥ z`:
`ω(log n / log z) / log z` is the prime density `1 / log n` plus the sum over the levels
`z ≤ k < n` of the densities `ω(log (n / k) / log k) / (k log^2 k)`, up to `O(1 / z)`. This is
the telescoped form of `buchstab_step_error`. -/
theorem buchstab_telescope_term {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {M : ℝ} {z n : ℕ} (hz3 : 3 ≤ z) (hzn : z ≤ n) (hM : Real.log n ≤ M * Real.log z) :
    |ω (Real.log n / Real.log z) / Real.log z -
        (1 / Real.log n + ∑ k ∈ Finset.Ico z n,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
      (2 * M + 6) / (z : ℝ) := by
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
  have hz3' : (3 : ℝ) ≤ z := by exact_mod_cast hz3
  have hlz : 1 ≤ Real.log z :=
    (Real.le_log_iff_exp_le hz0).mpr (by linarith [Real.exp_one_lt_d9])
  have hln : 1 ≤ Real.log n :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have hM0 : 0 ≤ M := by nlinarith
  have tel := Finset.sum_Ico_sub (fun k : ℕ => ω (Real.log n / Real.log k) / Real.log k) hzn
  have hfn : ω (Real.log n / Real.log n) / Real.log n = 1 / Real.log n := by
    rw [div_self (by linarith), hω.2.1 1 le_rfl (by norm_num)]
    norm_num
  rw [hfn] at tel
  have e : ω (Real.log n / Real.log z) / Real.log z -
        (1 / Real.log n + ∑ k ∈ Finset.Ico z n,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)) =
      ∑ k ∈ Finset.Ico z n, (ω (Real.log n / Real.log k) / Real.log k -
        ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ) -
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)) := by
    rw [Finset.sum_sub_distrib]
    have tel' : ∑ k ∈ Finset.Ico z n, (ω (Real.log n / Real.log k) / Real.log k -
        ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ)) =
        ω (Real.log n / Real.log z) / Real.log z - 1 / Real.log n := by
      have hneg : ∑ k ∈ Finset.Ico z n, (ω (Real.log n / Real.log k) / Real.log k -
          ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ)) =
          -∑ k ∈ Finset.Ico z n, (ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) /
            Real.log ((k + 1 : ℕ) : ℝ) - ω (Real.log n / Real.log k) / Real.log k) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [hneg, tel]
      ring
    rw [tel']
    ring
  rw [e]
  have hterm : ∀ k ∈ Finset.Ico z n, |ω (Real.log n / Real.log k) / Real.log k -
        ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ) -
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)| ≤
      (M + 2) * (1 / (k : ℝ) ^ 2) + (if k = Nat.sqrt n then 2 / (k : ℝ) else 0) := by
    intro k hk
    obtain ⟨hzk, hkn⟩ := Finset.mem_Ico.mp hk
    have hlk : Real.log z ≤ Real.log k := Real.log_le_log hz0 (by exact_mod_cast hzk)
    have := buchstab_step_error hω hz (M := M) (by omega : 3 ≤ k) hkn
      (hM.trans (mul_le_mul_of_nonneg_left hlk hM0))
    rw [mul_one_div]
    exact this
  have hs1 := sum_inv_sq_Ico (by omega : 2 ≤ z) n hzn
  have hs2 : ∑ k ∈ Finset.Ico z n, (if k = Nat.sqrt n then 2 / (k : ℝ) else 0) ≤ 2 / (z : ℝ) := by
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · have hzs : (z : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp h).1
      exact div_le_div_of_nonneg_left (by norm_num) hz0 hzs
    · positivity
  calc _ ≤ ∑ k ∈ Finset.Ico z n, |ω (Real.log n / Real.log k) / Real.log k -
        ω (Real.log n / Real.log ((k + 1 : ℕ) : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ) -
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico z n, ((M + 2) * (1 / (k : ℝ) ^ 2) +
          (if k = Nat.sqrt n then 2 / (k : ℝ) else 0)) := Finset.sum_le_sum hterm
    _ = (M + 2) * ∑ k ∈ Finset.Ico z n, 1 / (k : ℝ) ^ 2 +
          ∑ k ∈ Finset.Ico z n, (if k = Nat.sqrt n then 2 / (k : ℝ) else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (M + 2) * (2 / (z : ℝ)) + 2 / (z : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hs1 (by linarith)) hs2
    _ = _ := by ring

/-- P0069 page 51, display 5.17: a negative power of `X` is below any negative power of
`log X`, the form in which errors of size `b / z` with `z ≥ X ^ c` are absorbed. -/
theorem rpow_neg_le_log_rpow_neg {c A : ℝ} (hc : 0 < c) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 3 ≤ X → X ^ (-c) ≤ K * Real.log X ^ (-A) := by
  have hε : 0 < c / A := div_pos hc hA
  refine ⟨(1 / (c / A)) ^ A, by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have h1 : Real.log X ≤ X ^ (c / A) / (c / A) := Real.log_le_rpow_div hX0.le hε
  have h2 : Real.log X ^ A ≤ (1 / (c / A)) ^ A * X ^ c := by
    calc Real.log X ^ A ≤ (X ^ (c / A) / (c / A)) ^ A := Real.rpow_le_rpow hlog.le h1 hA.le
      _ = (1 / (c / A)) ^ A * X ^ c := by
          rw [div_eq_mul_one_div, mul_comm, Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul hX0.le]
          congr 2
          field_simp
  rw [Real.rpow_neg hX0.le, Real.rpow_neg hlog.le, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  linarith

/-- P0069 page 51, display 5.17, the continuous Buchstab identity summed over an interval:
the Buchstab density sum at level `z` over `(a, b]` is the sum of the prime densities
`1 / log n`, `n ≥ z`, plus the sum over levels `z ≤ k < n` of the densities
`ω(log (n / k) / log k) / (k log^2 k)`, with every log power saved. -/
theorem buchstab_telescope (ω : ℝ → ℝ) (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log n else 0) +
            ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
          C * b * Real.log X ^ (-A) := by
  obtain ⟨K, hK, hKX⟩ := rpow_neg_le_log_rpow_neg hc hA
  have hc6 : 0 < 2 * (1 / c) + 6 := by positivity
  refine ⟨max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) * K, by positivity,
    fun X hX z hzX a b ha hb => ?_⟩
  have hK2 : 0 < (2 * (1 / c) + 6) * K := by positivity
  have hX3 : 3 ≤ X := by linarith [le_max_right ((3 : ℝ) ^ (1 / c)) 3]
  have hXc : (3 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((3 : ℝ) ^ (1 / c)) 3]
  have hX0 : 0 < X := by linarith
  have h3z : (3 : ℝ) ≤ z := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  have hz3 : 3 ≤ z := by exact_mod_cast h3z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
      (2 * (1 / c) + 6) / (z : ℝ) := by
    intro n hn
    obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    by_cases hzn : z ≤ n
    · rw [ite_eq_left hzn]
      refine buchstab_telescope_term hω hz hz3 hzn ?_
      exact (Real.log_le_log hn0 (le_trans (by exact_mod_cast hnb) hb)).trans hlogz
    · rw [ite_eq_right hzn, Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, add_zero,
        sub_zero]
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log hn0 (by exact_mod_cast (by omega : n < z))
      rw [hz _ hu, zero_div, abs_zero]
      positivity
  have hzinv : 1 / (z : ℝ) ≤ K * Real.log X ^ (-A) := by
    have h1 : 1 / (z : ℝ) ≤ X ^ (-c) := by
      rw [Real.rpow_neg hX0.le, one_div]
      exact inv_anti₀ (Real.rpow_pos_of_pos hX0 c) hzX
    exact h1.trans (hKX X hX3)
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hLA : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlogX.le _
  calc _ ≤ ∑ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc a b, (2 * (1 / c) + 6) / (z : ℝ) := Finset.sum_le_sum hterm
    _ = ((b - a : ℕ) : ℝ) * ((2 * (1 / c) + 6) * (1 / (z : ℝ))) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        ring
    _ ≤ (b : ℝ) * ((2 * (1 / c) + 6) * (K * Real.log X ^ (-A))) := by
        have : ((b - a : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b a
        gcongr
    _ = (2 * (1 / c) + 6) * K * b * Real.log X ^ (-A) := by ring
    _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) * K) * b * Real.log X ^ (-A) := by
        have : (0 : ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
        gcongr
        linarith

end LeanLab.BHP1997.LowerShortC165
