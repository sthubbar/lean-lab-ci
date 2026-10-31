/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 4, displays (4.8)-(4.9).
`SizeProp A` of `Section4.lean`, the asymptotic half of (4.8)-(4.9), PROVED for every `A ≥ 1`,
unconditionally, from Mathlib's Chebyshev lower bound `Chebyshev.theta_ge`
(`θ(n) ≥ n log 2 - log(n+1) - 2√n log n`) and upper bound `Chebyshev.theta_le_log4_mul_x`.

Route, OUR OWN and simpler than the paper's 1/3-exponent count: for primes `p ≥ 4096`,
`#L_p ≤ 3 a_p` and `9 a_p² ≤ p`, so `#L_p² ≤ p`; for `p < 4096`, `#L_p² ≤ p · p`.
Hence `(∏ #L_p)² ≤ q_0 · q_0(4096)`. Since `log 2 > 2/3`, `θ(Z) ≥ 2Z/3 + C` eventually, which
beats `(log u)^{2A} ≤ exp(2Z/3)` with `Z = ⌈3A log log u⌉`. The `+1` term uses `q_0 ≤ 4^Z ≤ u`.

AI-written Lean code, Claude, run 20261021T0103Z-19411, unit U-1308. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Section4

open Finset Filter Real Asymptotics
open scoped Classical Chebyshev

noncomputable section
namespace LeanLab.SparseTernary.SizeProof

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4

/-- For `p ≥ 4096 = 16³`, `9 a_p² ≤ p`, where `a_p = ⌈p^{1/3}⌉ + 1`. -/
theorem nine_aOf_sq_le (p : ℕ) (hp : 4096 ≤ p) : 9 * aOf p ^ 2 ≤ p := by
  set s : ℝ := (p : ℝ) ^ ((1 : ℝ) / 3) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs3 : s ^ 3 = (p : ℝ) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hp' : (4096 : ℝ) ≤ p := by exact_mod_cast hp
  have hs16 : 16 ≤ s := by
    by_contra h
    push_neg at h
    have : s ^ 3 < 16 ^ 3 := pow_lt_pow_left₀ h hs0 (by norm_num)
    rw [hs3] at this; linarith
  have ha : (aOf p : ℝ) ≤ s + 2 := by
    have := Nat.ceil_lt_add_one hs0
    unfold aOf; push_cast; linarith
  have ha0 : (0 : ℝ) ≤ aOf p := Nat.cast_nonneg _
  have key : (9 * aOf p ^ 2 : ℝ) ≤ p := by
    rw [← hs3]
    have h1 : (aOf p : ℝ) ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs16) (sq_nonneg s), sq_nonneg (s - 16)]
  exact_mod_cast key

/-- Per prime: `#L_p² ≤ p · (p if p < 4096 else 1)`. -/
theorem card_Lset_sq_le (p : ℕ) (hp : p.Prime) :
    #(Lset p) ^ 2 ≤ p * (if p < 4096 then p else 1) := by
  split_ifs with h
  · have := card_Lset_le_pred p hp.pos
    calc #(Lset p) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = p * p := sq p
  · push_neg at h
    have h1 := card_Lset_le p
    have h2 := nine_aOf_sq_le p h
    calc #(Lset p) ^ 2 ≤ (3 * aOf p) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 9 * aOf p ^ 2 := by ring
      _ ≤ p := h2
      _ = p * 1 := (mul_one p).symm

/-- `(∏_{p<Z} #L_p)² ≤ q_0(Z) · q_0(4096)`. -/
theorem prod_sq_le (Z : ℕ) :
    (∏ p ∈ Nat.primesBelow Z, #(Lset p)) ^ 2 ≤ q0 Z * q0 4096 := by
  rw [← prod_pow]
  have hsub : (Nat.primesBelow Z).filter (· < 4096) ⊆ Nat.primesBelow 4096 := by
    intro x hx
    simp only [mem_filter, Nat.mem_primesBelow] at hx ⊢
    exact ⟨hx.2, hx.1.2⟩
  calc ∏ p ∈ Nat.primesBelow Z, #(Lset p) ^ 2
      ≤ ∏ p ∈ Nat.primesBelow Z, (p * if p < 4096 then p else 1) :=
        Finset.prod_le_prod
          (fun p hp => card_Lset_sq_le p (Nat.prime_of_mem_primesBelow hp))
    _ = q0 Z * ∏ p ∈ Nat.primesBelow Z, (if p < 4096 then p else 1) := by
        rw [prod_mul_distrib]; rfl
    _ ≤ q0 Z * q0 4096 := by
        refine Nat.mul_le_mul_left _ ?_
        rw [← prod_filter]
        exact Nat.le_of_dvd (q0_pos _) (prod_dvd_prod_of_subset _ _ _ hsub)

/-- `log q_0(Z) = θ(Z - 1)`. -/
theorem log_q0 (Z : ℕ) : Real.log (q0 Z) = θ ((Z - 1 : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  unfold q0
  rw [Nat.primesBelow_eq_primesLE_sub_one]
  rfl

/-- Chebyshev, the form we need: for any constant `K`, eventually `K + 2(n+1)/3 ≤ θ(n)`.
Uses `log 2 > 2/3` and Mathlib's `theta_ge`. -/
theorem theta_eventually (K : ℝ) : ∀ᶠ n : ℕ in atTop, K + 2 * ((n : ℝ) + 1) / 3 ≤ θ (n : ℝ) := by
  have h1 : (fun x : ℝ => Real.log (x + 1)) =o[atTop] (id : ℝ → ℝ) := by
    have := isLittleO_log_id_atTop.comp_tendsto (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    refine this.trans_isBigO ?_
    have hb : (fun x : ℝ => x + 1) =O[atTop] (id : ℝ → ℝ) :=
      (isBigO_refl (id : ℝ → ℝ) atTop).add (isLittleO_const_id_atTop (1 : ℝ)).isBigO
    exact hb
  have h2 : (fun x : ℝ => 2 * √x * Real.log x) =o[atTop] (id : ℝ → ℝ) := by
    have hl : Real.log =o[atTop] (fun x : ℝ => √x) :=
      (isLittleO_log_rpow_atTop (r := 1 / (2 : ℝ)) (by norm_num)).congr_right
        (fun x => (Real.sqrt_eq_rpow x).symm)
    have := (isBigO_refl (fun x : ℝ => 2 * √x) atTop).mul_isLittleO hl
    refine this.trans_isBigO ?_
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have : 2 * √x * √x = 2 * x := by rw [mul_assoc, Real.mul_self_sqrt hx]
    rw [this]
    simp [abs_of_nonneg hx]
  have h3 : (fun x : ℝ => Real.log (x + 1) + 2 * √x * Real.log x + (K + 2 / 3)) =o[atTop]
      (id : ℝ → ℝ) := (h1.add h2).add (isLittleO_const_id_atTop _)
  have hc : (0 : ℝ) < Real.log 2 - 2 / 3 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have h4 := tendsto_natCast_atTop_atTop.eventually (h3.def hc)
  filter_upwards [h4] with n hn
  have ht := Chebyshev.theta_ge n
  have hle : Real.log ((n : ℝ) + 1) + 2 * √(n : ℝ) * Real.log n + (K + 2 / 3) ≤
      (Real.log 2 - 2 / 3) * n := by
    refine (le_abs_self _).trans ?_
    have := hn
    simp only [Real.norm_eq_abs, id, Nat.abs_cast] at this
    exact this
  nlinarith

theorem tendsto_Zof (A : ℕ) (hA : 1 ≤ A) : Tendsto (fun u => Zof A u) atTop atTop := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hA' : (0 : ℝ) < 3 * A := by linarith
  have : Tendsto (fun u => 3 * (A : ℝ) * Real.log (Real.log u)) atTop atTop :=
    Tendsto.const_mul_atTop hA' (tendsto_log_atTop.comp tendsto_log_atTop)
  exact tendsto_nat_ceil_atTop.comp this

/-- The final algebra of `sizeProp`, isolated: from `LA² ≤ E`, `4 M E ≤ q`, `q ≤ u` and
`P² ≤ q M` we get `P (u/q + 1) ≤ u / LA`. -/
theorem final_alg (u LA P q M E : ℝ) (hLA0 : 0 < LA) (hP0 : 0 ≤ P) (hq0 : 0 < q)
    (hM0 : 0 < M) (h1 : LA ^ 2 ≤ E) (hd : 4 * M * E ≤ q) (he : q ≤ u) (ha : P ^ 2 ≤ q * M) :
    P * (u / q + 1) ≤ u / LA := by
  have hsq : (2 * LA * P) ^ 2 ≤ q ^ 2 := by
    have hE : 0 ≤ E := (sq_nonneg LA).trans h1
    have s1 : 4 * LA ^ 2 * P ^ 2 ≤ 4 * E * (q * M) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) ha (sq_nonneg P) (by positivity)
    have s2 : q * (4 * M * E) ≤ q * q := mul_le_mul_of_nonneg_left hd hq0.le
    nlinarith
  have h2 : 2 * LA * P ≤ q :=
    (pow_le_pow_iff_left₀ (by positivity) hq0.le (by norm_num)).1 hsq
  rw [le_div_iff₀ hLA0]
  have hu : 0 < u := lt_of_lt_of_le hq0 he
  have k1 : P * LA * u / q ≤ u / 2 := by
    rw [div_le_iff₀ hq0]; nlinarith
  have k2 : P * LA ≤ u / 2 := by linarith
  have k3 : P * (u / q + 1) * LA = P * LA * u / q + P * LA := by field_simp
  linarith

/-- **`SizeProp A` for every `A ≥ 1`, PROVED unconditionally**: the asymptotic half of
(4.8)-(4.9). Eventually `(∏_{p<z} #L_p)(u/q_0 + 1) ≤ u/(log u)^A` with `z = 3A log log u`. -/
theorem sizeProp (A : ℕ) (hA : 1 ≤ A) : SizeProp A := by
  obtain ⟨M', hM'0, hM'⟩ : ∃ M' : ℕ, 0 < M' ∧
      ∀ Z, (∏ p ∈ Nat.primesBelow Z, #(Lset p)) ^ 2 ≤ q0 Z * M' :=
    ⟨q0 4096, q0_pos _, prod_sq_le⟩
  obtain ⟨M, hM, hM0⟩ : ∃ M : ℝ, M = (M' : ℝ) ∧ 0 < M := ⟨M', rfl, by exact_mod_cast hM'0⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (theta_eventually (Real.log (4 * M)))
  have hZ : ∀ᶠ u in atTop, N + 1 ≤ Zof A u := tendsto_atTop.1 (tendsto_Zof A hA) (N + 1)
  have hCpos : (0 : ℝ) < 3 * A * Real.log 4 := by
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have hL : ∀ᶠ u in atTop, 3 * A * Real.log 4 * Real.log (Real.log u) ≤ Real.log u := by
    have hw : ∀ᶠ w : ℝ in atTop, 3 * A * Real.log 4 * Real.log w ≤ w := by
      have := isLittleO_log_id_atTop.def (inv_pos.mpr hCpos)
      filter_upwards [this, eventually_ge_atTop (0 : ℝ)] with w hw hw0
      simp only [Real.norm_eq_abs, id, abs_of_nonneg hw0] at hw
      have h1 : Real.log w ≤ (3 * A * Real.log 4)⁻¹ * w := (le_abs_self _).trans hw
      calc 3 * A * Real.log 4 * Real.log w ≤ 3 * A * Real.log 4 * ((3 * A * Real.log 4)⁻¹ * w) :=
            mul_le_mul_of_nonneg_left h1 hCpos.le
        _ = w := by field_simp
    exact tendsto_log_atTop.eventually hw
  have hu1 : ∀ᶠ u in atTop, Real.exp 1 ≤ u := eventually_ge_atTop _
  obtain ⟨u0, hu0⟩ := eventually_atTop.1 (hZ.and (hL.and hu1))
  refine ⟨u0, fun u hu => ?_⟩
  obtain ⟨hZu, hLu, he⟩ := hu0 u hu
  have hu_pos : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) he
  have hlogu : 1 ≤ Real.log u := (Real.le_log_iff_exp_le hu_pos).2 he
  have hll : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hlogu
  set Z := Zof A u with hZdef
  have hZge : 3 * A * Real.log (Real.log u) ≤ (Z : ℝ) := Nat.le_ceil _
  have hZ1 : 1 ≤ Z := by omega
  have hcast : ((Z - 1 : ℕ) : ℝ) + 1 = Z := by push_cast [Nat.cast_sub hZ1]; ring
  set P : ℝ := ((∏ p ∈ Nat.primesBelow Z, #(Lset p) : ℕ) : ℝ) with hP
  set q : ℝ := (q0 Z : ℝ) with hq
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast q0_pos Z
  set LA : ℝ := Real.log u ^ A with hLA
  have hLA0 : 0 < LA := by positivity
  -- (c) `(log u)^A ≤ exp(Z/3)`
  have hLAle : LA ≤ Real.exp ((Z : ℝ) / 3) := by
    rw [hLA, ← Real.exp_log (by linarith : 0 < Real.log u), ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by linarith)
  -- (d) `4 M exp(2Z/3) ≤ q`, from Chebyshev
  have hθ := hN (Z - 1) (by omega)
  rw [hcast, ← log_q0 Z] at hθ
  have hd : 4 * M * Real.exp (2 * (Z : ℝ) / 3) ≤ q := by
    have := Real.exp_le_exp.2 hθ
    rwa [Real.exp_add, Real.exp_log (by positivity), Real.exp_log hq0] at this
  -- (e) `q ≤ u`, from `θ(x) ≤ x log 4`
  have he' : q ≤ u := by
    have h1 : Real.log q ≤ Real.log 4 * ((Z - 1 : ℕ) : ℝ) := by
      rw [hq, log_q0 Z]; exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
    have h2 : ((Z - 1 : ℕ) : ℝ) ≤ 3 * A * Real.log (Real.log u) := by
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * A * Real.log (Real.log u) by positivity)
      have h3 : ((Z : ℕ) : ℝ) < 3 * A * Real.log (Real.log u) + 1 := this
      linarith
    have h4 : Real.log q ≤ Real.log u := by
      have : Real.log 4 * ((Z - 1 : ℕ) : ℝ) ≤ Real.log 4 * (3 * A * Real.log (Real.log u)) :=
        mul_le_mul_of_nonneg_left h2 (Real.log_nonneg (by norm_num))
      nlinarith
    rw [← Real.exp_log hq0, ← Real.exp_log hu_pos]; exact Real.exp_le_exp.2 h4
  -- (a) `P² ≤ q M`
  have ha : P ^ 2 ≤ q * M := by
    rw [hP, hq, hM]; exact_mod_cast hM' Z
  -- combine: `2 LA P ≤ q`
  have hexp : Real.exp ((Z : ℝ) / 3) ^ 2 = Real.exp (2 * (Z : ℝ) / 3) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h1 : LA ^ 2 ≤ Real.exp (2 * (Z : ℝ) / 3) := by
    have := pow_le_pow_left₀ hLA0.le hLAle 2
    rwa [hexp] at this
  exact final_alg u LA P q M _ hLA0 hP0 hq0 hM0 h1 hd he' ha

/-- `SizeProp A` for every positive `A`. -/
theorem sizeProp_all : ∀ A : ℕ, 0 < A → SizeProp A := fun A hA => sizeProp A hA

/-- **Lemma 3.1 for every positive `A`, CONDITIONAL ON `RepProp A` only.** -/
theorem lemma31_of_repProp (hR : ∀ A : ℕ, 0 < A → RepProp A) :
    ∀ A : ℕ, 0 < A → Lemma31 A :=
  lemma31_all_of_props sizeProp_all hR

/-- Vacuity test for `sizeProp`: `A = 1` is a legitimate instance, so the theorem is not empty. -/
example : SizeProp 1 := sizeProp 1 le_rfl

end LeanLab.SparseTernary.SizeProof

#print axioms LeanLab.SparseTernary.SizeProof.sizeProp
#print axioms LeanLab.SparseTernary.SizeProof.lemma31_of_repProp
