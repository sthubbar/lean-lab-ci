/-
Burst 2026-11-22, BHP1997, session S131, step window-s113-p2. Split of the LEAF
`S113WindowRough.leaf_prime_weight_transfer_window`, P0069 Baker Harman Pintz 1997, page 51,
display 5.17: "a straightforward consequence of the prime number theorem, with error term
`Y exp(-ε L^(1/2))`", in the Buchstab recursion over the least prime factor `p ≥ z` of the rough
cofactor of display 5.15, page 50.

The cut is the one of the proved log power route `LowerShortC165.prime_weight_transfer` of
`RoughDensity517d`: the abstract partial summation `LowerShortC165.prime_transfer_abstract`,
PROVED, applied with the prime count input at every level `X ^ c ≤ Y ≤ X`. That one input is
left as a LEAF, now with the error of 5.17:
* `leaf_prime_prefix_level_window`, the prime number theorem for the prime count on `(L, i]`
  against the discrete logarithmic integral, error `Y exp(-N (log X)^(1/3))`; the window form of
  the PROVED `LowerShortC165.prime_prefix_level`. Route: partial summation from
  `DQ517StrongPNTInput.psi_error_stretched`.

PROVED here from that leaf: `exp_log_sq_absorb`, the bookkeeping that one more unit of `N`
absorbs `log^2 X`, and `leaf_prime_weight_transfer_window_split`, with exactly the statement of
`S113WindowRough.leaf_prime_weight_transfer_window`.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.S113WindowRough

namespace LeanLab.BHP1997.S131WindowPrimeTransfer
open Classical
open scoped BigOperators
open LeanLab.BHP1997.Decomp132 (primeWeight)
open LeanLab.BHP1997.LowerShortC165
  (prime_transfer_abstract density_level_step abs_buchstab_le_one)

/-- LEAF: page 51 display 5.17, its prime number theorem input at a level, with the error of
5.17. HARD. For `X ^ c ≤ Y ≤ X` the prime count on any `(L, i]` with `i ≤ Y` is the sum of
`1 / log k` over the same interval up to `Y exp(-N (log X)^(1/3))`. Window form of the PROVED
`LowerShortC165.prime_prefix_level`; route: partial summation in `θ` from
`DQ517StrongPNTInput.psi_error_stretched`, the prime number theorem with de la Vallee Poussin
error, plus the trivial bound below `X ^ (c / 2)`. -/
theorem leaf_prime_prefix_level_window {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ X : ℝ, Cq ≤ X → ∀ Y : ℝ, X ^ c ≤ Y → Y ≤ X →
      ∀ L i : ℕ, L ≤ i → (i : ℝ) ≤ Y →
        |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤
          Cq * Y * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  sorry

/-- Page 51 display 5.17, the error bookkeeping of the transfer: one more unit of `N` absorbs
the factor `log^2 X` of partial summation, since `log^2 X = l ^ 6 ≤ 720 e ^ l` with
`l = (log X)^(1/3)`. -/
theorem exp_log_sq_absorb {X : ℝ} (hX : 1 ≤ X) (N : ℝ) :
    Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X ^ 2 ≤
      720 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  have hlx : 0 ≤ Real.log X := Real.log_nonneg hX
  set l := Real.log X ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log X := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have h2 := Real.pow_div_factorial_le_exp l hl0 6
  have hfac : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hfac] at h2
  have hsplit : Real.exp (-(N + 1) * l) = Real.exp (-N * l) * Real.exp (-l) := by
    rw [← Real.exp_add]; ring_nf
  have hel : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
  have hE0 : 0 < Real.exp (-N * l) := Real.exp_pos _
  have hm0 : 0 < Real.exp (-l) := Real.exp_pos _
  rw [hsplit, ← hl3]
  have key : Real.exp (-l) * (l ^ 3) ^ 2 ≤ 720 := by
    have h6 : l ^ 6 ≤ 720 * Real.exp l := by
      linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 720)).mp h2]
    have e : (l ^ 3) ^ 2 = l ^ 6 := by ring
    rw [e]
    calc Real.exp (-l) * l ^ 6 ≤ Real.exp (-l) * (720 * Real.exp l) :=
          mul_le_mul_of_nonneg_left h6 hm0.le
      _ = 720 * (Real.exp (-l) * Real.exp l) := by ring
      _ = 720 := by rw [hel, mul_one]
  calc Real.exp (-N * l) * Real.exp (-l) * (l ^ 3) ^ 2
      = Real.exp (-N * l) * (Real.exp (-l) * (l ^ 3) ^ 2) := by ring
    _ ≤ Real.exp (-N * l) * 720 := mul_le_mul_of_nonneg_left key hE0.le
    _ = 720 * Real.exp (-N * l) := by ring

/-- PROVED from `leaf_prime_prefix_level_window`: page 51 display 5.17, the prime number
theorem applied to the least prime factor `p ≥ z` in the Buchstab recursion for the rough
cofactor of display 5.15, with the error `b exp(-N (log X)^(1/3))` of 5.17. Exactly the
statement of the LEAF `S113WindowRough.leaf_prime_weight_transfer_window`, to be wired by the
lab gate. The proof is that of `LowerShortC165.prime_weight_transfer` with the window prime
input. -/
theorem leaf_prime_weight_transfer_window_split (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            ((if a < k then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
                ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨Cq, hCq, hpnt⟩ := leaf_prime_prefix_level_window hc (N + 1) (by linarith)
  have hE : (0 : ℝ) ≤ 2 / c + 1 := by positivity
  refine ⟨max ((4 : ℝ) ^ (1 / c)) 4 + Cq + 720 * ((3 + 4 * (2 / c + 1)) * Cq), by positivity,
    fun X hX z hzX a b ha hb => ?_⟩
  have hpos2 : 0 < 720 * ((3 + 4 * (2 / c + 1)) * Cq) := by positivity
  have hX4 : 4 ≤ X := by linarith [le_max_right ((4 : ℝ) ^ (1 / c)) 4]
  have hXc : (4 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((4 : ℝ) ^ (1 / c)) 4]
  have hXq : Cq ≤ X := by
    have : (0 : ℝ) ≤ max ((4 : ℝ) ^ (1 / c)) 4 := by positivity
    linarith
  have hX0 : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 < Real.log X := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hEN : 0 ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  have hr0 : 0 ≤ Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  have h4z : (4 : ℝ) ≤ z := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  have hz4 : 4 ≤ z := by exact_mod_cast h4z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogk : ∀ k : ℕ, 3 ≤ k → 1 ≤ Real.log k := by
    intro k hk
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  by_cases hzb : z ≤ b
  swap
  · have hK : (Finset.Icc 1 b).filter (fun k => z ≤ k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    have hP : (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    rw [hK, hP, Finset.sum_empty, Finset.sum_empty, sub_zero, abs_zero]
    positivity
  have hmain := prime_transfer_abstract
    (fun m k : ℕ => ω (Real.log m / Real.log k) / Real.log k) (a := a)
    (E := 2 / c + 1) (R := Cq * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)))
    (by omega : 2 ≤ z) hzb hE
    (by positivity)
    (by
      intro m k hm hmk
      have hl := hlogk k (by omega)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hu : Real.log m / Real.log k < 1 := by
        rw [div_lt_one (by linarith)]
        exact Real.log_lt_log hm0 (by exact_mod_cast hmk)
      rw [hz _ hu, zero_div])
    (by
      intro m i hzi him hmb
      have hi3 : 3 ≤ i := by omega
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hi2 : i + 1 ≤ i ^ 2 := by nlinarith
      have hzi2 : z ≤ i ^ 2 := le_trans (by omega) hi2
      have h1 : Real.log z ≤ 2 * Real.log i := by
        have := Real.log_le_log hz0 (by exact_mod_cast hzi2 : (z : ℝ) ≤ (i : ℝ) ^ 2)
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have h2 : Real.log m ≤ Real.log X :=
        Real.log_le_log hm0 (le_trans (by exact_mod_cast hmb) hb)
      have h3 : 1 / c * Real.log z ≤ 1 / c * (2 * Real.log i) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have hM : Real.log m ≤ 2 / c * Real.log i := by
        have e : 1 / c * (2 * Real.log i) = 2 / c * Real.log i := by ring
        linarith
      exact density_level_step hω hz hi3 him hM)
    (by
      intro m k hzk
      have hl := hlogk k (by omega)
      rw [abs_div, abs_of_pos (by linarith : 0 < Real.log k)]
      exact (div_le_one (by linarith)).mpr ((abs_buchstab_le_one hω hz _).trans hl))
    (by
      intro Y hzY hYb L i hLi hiY
      exact le_of_le_of_eq (hpnt X hXq Y (hzX.trans hzY) (hYb.trans hb) L i hLi hiY) (by ring))
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
  have hlb : Real.log b ≤ Real.log X := Real.log_le_log hbpos hb
  have habs := exp_log_sq_absorb (by linarith : (1 : ℝ) ≤ X) N
  have h1 : 1 + Real.log b ≤ 2 * Real.log X := by linarith
  have h2 : 1 + (2 / c + 1) * (1 + Real.log b) ≤ (1 + 2 * (2 / c + 1)) * Real.log X := by
    nlinarith
  have h3 : (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b) ≤
      ((1 + 2 * (2 / c + 1)) * Real.log X) * (2 * Real.log X) :=
    mul_le_mul h2 h1 (by linarith) (by positivity)
  have h4 : 1 ≤ Real.log X ^ 2 := by nlinarith
  have hCb : 0 ≤ Cq * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * b := by positivity
  calc _ ≤ Cq * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * b +
        (1 + (2 / c + 1) * (1 + Real.log b)) *
        (Cq * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * b * (1 + Real.log b)) := hmain
    _ = Cq * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * b *
        (1 + (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b)) := by ring
    _ ≤ Cq * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * b *
        ((3 + 4 * (2 / c + 1)) * Real.log X ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hCb
        nlinarith
    _ = (3 + 4 * (2 / c + 1)) * Cq * b *
        (Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * Real.log X ^ 2) := by ring
    _ ≤ (3 + 4 * (2 / c + 1)) * Cq * b *
        (720 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by
        have : 0 ≤ (3 + 4 * (2 / c + 1)) * Cq * b := by positivity
        exact mul_le_mul_of_nonneg_left habs this
    _ = 720 * ((3 + 4 * (2 / c + 1)) * Cq) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        ring
    _ ≤ _ := by
        have : (0 : ℝ) ≤ max ((4 : ℝ) ^ (1 / c)) 4 := by positivity
        gcongr
        linarith

end LeanLab.BHP1997.S131WindowPrimeTransfer
