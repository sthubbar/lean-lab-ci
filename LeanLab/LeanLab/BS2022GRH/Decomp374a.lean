/- AI wrote this Lean code for CODEX task374. Goldbach is open.
The two separate large sieve moments behind journal display 15, p. 1225.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp148a
import LeanLab.PNTPort.LargeSieve.Bilinear
import LeanLab.Linnik.HilbertCosecant

namespace LeanLab.BS2022GRH.Decomp374a
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The moduli in one dyadic block, journal p. 1225 display 15. -/
def blockModuli (R : ℝ) : Finset ℕ :=
  (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ))

/-- Primitive characters in that block, journal p. 1225 display 15. -/
def blockCharacters (R : ℝ) : Finset (Σ r : ℕ, DirichletCharacter ℂ r) :=
  (blockModuli R).sigma (fun r =>
    (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive))

/-- One quadratic moment with the standard r over phi r weight, display 15. -/
def blockEnergy (R : ℝ) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ i ∈ blockCharacters R, ((i.1 : ℝ) / i.1.totient) *
    ‖∑ n ∈ S, a n * i.2 n‖ ^ 2

/-! ### Private helpers: the sharp large sieve

`coefficient_energy` sits on the sharp constant `N + Q²` of Selberg's character large sieve, so the
lab's `N + 2Q²` sieve cannot close it. The chain below is the lab's sharp development
(`LeanLab.Linnik.Decomp1532b`), ported here as private helpers because that module's import closure
still carries other units' open leaves: Montgomery-Vaughan's circular Hilbert inequality
(`LeanLab.Linnik.HilbertCosecant.cosecant_hilbert`, the one added import), Gallagher's double-ended
geometric kernel, exact finite duality, and the Farey/character reduction. -/
/-- `(Ioc M (M + N)).card = N` for `ℤ`-indexed intervals. -/
private lemma card_Ioc_int_eq (M : ℤ) (N : ℕ) : (Ioc M (M + N)).card = N := by
  rw [Int.card_Ioc]; omega

/-- Duality: a dual bound with constant `Δ ≥ 0` gives the primal bound with the same `Δ`. -/
private lemma primal_of_dual {ι : Type*} [DecidableEq ι] {s : Finset ι} {α : ι → ℝ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (M : ℤ) (N : ℕ)
    (hdual : ∀ b : ι → ℂ,
      ∑ n ∈ Ioc M (M + N), ‖LeanLab.PNTPort.LargeSieve.dualSum s α b n‖ ^ 2 ≤
        Δ * ∑ r ∈ s, ‖b r‖ ^ 2)
    (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 ≤
      Δ * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  set I := Ioc M (M + N)
  set S : ι → ℂ := fun r => ∑ n ∈ I, a n * LeanLab.PNTPort.LargeSieve.e (n * α r) with hS
  set b : ι → ℂ := fun r => (starRingEnd ℂ) (S r) with hb
  set X := ∑ r ∈ s, ‖S r‖ ^ 2 with hXdef
  have hX0 : 0 ≤ X := sum_nonneg (fun _ _ => by positivity)
  have hX : (X : ℂ) = ∑ n ∈ I, a n * LeanLab.PNTPort.LargeSieve.dualSum s α b n := by
    rw [hXdef, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_pow, ← Complex.conj_mul']
    unfold LeanLab.PNTPort.LargeSieve.dualSum
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro r _
    rw [hS, mul_sum]
    apply sum_congr rfl; intro n _
    rw [hb]
    ring
  have h1 : X ≤ ∑ n ∈ I, ‖a n‖ * ‖LeanLab.PNTPort.LargeSieve.dualSum s α b n‖ := by
    have : X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    rw [this, hX]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp_rw [norm_mul]
  have h2 := sum_mul_sq_le_sq_mul_sq I (fun n => ‖a n‖)
    (fun n => ‖LeanLab.PNTPort.LargeSieve.dualSum s α b n‖)
  have h3 := hdual b
  have hbX : ∑ r ∈ s, ‖b r‖ ^ 2 = X := by
    rw [hXdef]; apply sum_congr rfl; intro r _; rw [hb, Complex.norm_conj]
  rw [hbX] at h3
  set Aa := ∑ n ∈ I, ‖a n‖ ^ 2
  have hAa : 0 ≤ Aa := sum_nonneg (fun _ _ => by positivity)
  have key : X ^ 2 ≤ Aa * (Δ * X) := by
    calc X ^ 2 ≤ (∑ n ∈ I, ‖a n‖ * ‖LeanLab.PNTPort.LargeSieve.dualSum s α b n‖) ^ 2 :=
          pow_le_pow_left₀ hX0 h1 2
      _ ≤ Aa * ∑ n ∈ I, ‖LeanLab.PNTPort.LargeSieve.dualSum s α b n‖ ^ 2 := h2
      _ ≤ Aa * (Δ * X) := mul_le_mul_of_nonneg_left h3 hAa
  rcases eq_or_lt_of_le hX0 with h | h
  · rw [← h]; positivity
  · have : X * X ≤ X * (Δ * Aa) := by nlinarith
    exact le_of_mul_le_mul_left this h

/-- Exact diagonal and off-diagonal Fourier energy identity (Gallagher 1975). -/
private lemma fourier_energy_split {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : Finset ℤ) (α : ι → ℝ) (b : ι → ℂ) :
    ∑ n ∈ t, ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 =
      (t.card : ℝ) * ∑ r ∈ s, ‖b r‖ ^ 2 +
      ∑ r ∈ s, ∑ r' ∈ s.erase r,
        (b r * (starRingEnd ℂ) (b r') *
          ∑ n ∈ t, LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
  classical
  have hn (n : ℤ) : ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 =
      ∑ r ∈ s, ∑ r' ∈ s, (b r * (starRingEnd ℂ) (b r') *
        LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
    have h := congrArg Complex.re (LeanLab.PNTPort.LargeSieve.normSq_dualSum s α b n)
    simpa only [LeanLab.PNTPort.LargeSieve.dualSum, Complex.ofReal_re, Complex.re_sum] using h
  simp_rw [hn]
  rw [sum_comm]
  have hr (r : ι) (hr : r ∈ s) :
      (∑ n ∈ t, ∑ r' ∈ s,
        (b r * (starRingEnd ℂ) (b r') *
          LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re) =
      (t.card : ℝ) * ‖b r‖ ^ 2 + ∑ r' ∈ s.erase r,
        (b r * (starRingEnd ℂ) (b r') *
          ∑ n ∈ t, LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re := by
    rw [sum_comm]
    rw [← sum_erase_add _ _ hr]
    simp only [sub_self, mul_zero, LeanLab.PNTPort.LargeSieve.e_zero, mul_one,
      Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, sum_const, nsmul_eq_mul]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro r' hr'
    rw [mul_sum, Complex.re_sum]
  rw [sum_congr rfl hr, sum_add_distrib, mul_sum]

/-- Normalization of the circular kernel (Montgomery and Vaughan 1974, pp. 73 to 82). -/
private lemma circular_kernel_eq_cosecant (θ : ℝ) :
    LeanLab.PNTPort.LargeSieve.e (θ / 2) /
        (LeanLab.PNTPort.LargeSieve.e θ - 1) =
      1 / (2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ)) := by
  have hx : LeanLab.PNTPort.LargeSieve.e θ =
      LeanLab.PNTPort.LargeSieve.e (θ / 2) ^ 2 := by
    rw [pow_two, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    ring
  have he : LeanLab.PNTPort.LargeSieve.e (θ / 2) ≠ 0 :=
    Complex.exp_ne_zero _
  have hs : LeanLab.PNTPort.LargeSieve.e (θ / 2) -
      (LeanLab.PNTPort.LargeSieve.e (θ / 2))⁻¹ =
      2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    have harg : Complex.I * ((2 * Real.pi * (θ / 2) : ℝ) : ℂ) =
        (Real.pi * θ : ℂ) * Complex.I := by push_cast; ring
    simp only [harg]
    rw [← Complex.exp_neg]
    rw [show -((Real.pi * θ : ℂ) * Complex.I) =
      (-((Real.pi * θ : ℂ))) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_mul, ← Complex.ofReal_sin]
    ring
  have hd : LeanLab.PNTPort.LargeSieve.e θ - 1 =
      LeanLab.PNTPort.LargeSieve.e (θ / 2) *
        (2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ)) := by
    rw [← hs, mul_sub, mul_inv_cancel₀ he, ← pow_two, ← hx]
  rw [hd, div_mul_eq_div_div, div_self he]

/-- The finite geometric kernel at both endpoints (Gallagher 1975 p. 131). -/
private lemma geometric_kernel_endpoints (M : ℤ) (N : ℕ) {θ : ℝ}
    (hθ : 0 < LeanLab.PNTPort.LargeSieve.dist0 θ) :
    ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * θ) =
      (LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + N + 1 / 2) * θ) -
        LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 / 2) * θ)) *
        (LeanLab.PNTPort.LargeSieve.e (θ / 2) /
          (LeanLab.PNTPort.LargeSieve.e θ - 1)) := by
  have hpos : 0 < ‖LeanLab.PNTPort.LargeSieve.e θ - 1‖ :=
    lt_of_lt_of_le (by linarith) (LeanLab.PNTPort.LargeSieve.four_dist0_le θ)
  have hne : LeanLab.PNTPort.LargeSieve.e θ ≠ 1 := by
    intro h
    simp [h] at hpos
  have hk : (∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * θ)) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) *
        ∑ k ∈ range N, LeanLab.PNTPort.LargeSieve.e (k * θ) := by
    rw [Int.Ioc_eq_finset_map, sum_map]
    simp only [add_sub_cancel_left, Int.toNat_natCast, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    push_cast
    ring
  have he1 : LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + N + 1 / 2) * θ) *
        LeanLab.PNTPort.LargeSieve.e (θ / 2) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) *
        LeanLab.PNTPort.LargeSieve.e (N * θ) := by
    rw [← LeanLab.PNTPort.LargeSieve.e_add, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    ring
  have he0 : LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1 / 2) * θ) *
        LeanLab.PNTPort.LargeSieve.e (θ / 2) =
      LeanLab.PNTPort.LargeSieve.e (((M : ℝ) + 1) * θ) := by
    rw [← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    ring
  rw [hk]
  simp_rw [LeanLab.PNTPort.LargeSieve.e_nat_mul]
  rw [geom_sum_eq hne]
  simp only [← mul_div_assoc, sub_mul, mul_sub, mul_one]
  rw [← LeanLab.PNTPort.LargeSieve.e_nat_mul, he1, he0]

/-- The circular Hilbert bound controls both endpoints of the geometric kernel. -/
private lemma offdiagonal_bound_of_hilbert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (hh : ∀ v : ι → ℂ,
      ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        v r * (starRingEnd ℂ) (v r') *
          (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
            (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
        (1 / (2 * δ)) * ∑ r ∈ s, ‖v r‖ ^ 2)
    (b : ι → ℂ) (M : ℤ) (N : ℕ) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N),
          LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))‖ ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  classical
  let H : (ι → ℂ) → ℂ := fun v => ∑ r ∈ s, ∑ r' ∈ s.erase r,
    v r * (starRingEnd ℂ) (v r') *
      (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
        (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))
  let v : ℝ → ι → ℂ := fun u r => b r * LeanLab.PNTPort.LargeSieve.e (u * α r)
  have hphase (u : ℝ) (r r' : ι) :
      v u r * (starRingEnd ℂ) (v u r') = b r * (starRingEnd ℂ) (b r') *
        LeanLab.PNTPort.LargeSieve.e (u * (α r - α r')) := by
    simp only [v, map_mul, ← LeanLab.PNTPort.LargeSieve.e_neg]
    rw [show u * (α r - α r') = u * α r + -(u * α r') by ring,
      LeanLab.PNTPort.LargeSieve.e_add]
    ring
  have henergy (u : ℝ) : ∑ r ∈ s, ‖v u r‖ ^ 2 = ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simp only [v, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one]
  have hH (u : ℝ) : ‖H (v u)‖ ≤ (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [henergy] using hh (v u)
  have heq : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))) =
      H (v ((M : ℝ) + N + 1 / 2)) - H (v ((M : ℝ) + 1 / 2)) := by
    simp only [H, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro r' hr'
    have hθ : 0 < LeanLab.PNTPort.LargeSieve.dist0 (α r - α r') :=
      hδ.trans_le (hs r hr r' (mem_erase.mp hr').2 (mem_erase.mp hr').1.symm)
    rw [geometric_kernel_endpoints M N hθ, hphase, hphase]
    ring
  rw [heq]
  calc
    _ ≤ ‖H (v ((M : ℝ) + N + 1 / 2))‖ + ‖H (v ((M : ℝ) + 1 / 2))‖ := norm_sub_le _ _
    _ ≤ (1 / (2 * δ)) * (∑ r ∈ s, ‖b r‖ ^ 2) +
        (1 / (2 * δ)) * (∑ r ∈ s, ‖b r‖ ^ 2) := add_le_add (hH _) (hH _)
    _ = _ := by ring

/-- The cosecant estimate gives the normalized circular estimate with its exact factor one half. -/
private lemma circular_hilbert_of_cosecant {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (b : ι → ℂ)
    (hh : ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
        b r * (starRingEnd ℂ) (b r') /
          (Real.sin (Real.pi * (α r - α r')) : ℂ)‖ ≤
        (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) :
    ‖∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))‖ ≤
      (1 / (2 * δ)) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  have he : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      b r * (starRingEnd ℂ) (b r') *
        (LeanLab.PNTPort.LargeSieve.e ((α r - α r') / 2) /
          (LeanLab.PNTPort.LargeSieve.e (α r - α r') - 1))) =
      (1 / (2 * Complex.I)) * ∑ r ∈ s, ∑ r' ∈ s.erase r,
        b r * (starRingEnd ℂ) (b r') /
          (Real.sin (Real.pi * (α r - α r')) : ℂ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    rw [mul_sum]
    apply sum_congr rfl
    intro r' hr'
    rw [circular_kernel_eq_cosecant]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hc : ‖(1 : ℂ) / (2 * Complex.I)‖ = 1 / 2 := by
    norm_num [norm_div, norm_mul]
  rw [he, norm_mul, hc]
  calc
    _ ≤ (1 / 2) * ((1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

/-- Exact finite duality preserves the sharp constant: sharp spaced sampling. -/
private lemma spaced_sampling_sharp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : LeanLab.PNTPort.LargeSieve.Spaced s α δ)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ r ∈ s, ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2 ≤
      ((N : ℝ) + 1 / δ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  apply primal_of_dual (by positivity) M N
  intro b
  change (∑ n ∈ Ioc M (M + N),
    ‖∑ r ∈ s, b r * LeanLab.PNTPort.LargeSieve.e (n * α r)‖ ^ 2) ≤ _
  rw [fourier_energy_split]
  have hcard : (Ioc M (M + (N : ℤ))).card = N := card_Ioc_int_eq M N
  rw [hcard]
  have hre : (∑ r ∈ s, ∑ r' ∈ s.erase r,
      (b r * (starRingEnd ℂ) (b r') *
        ∑ n ∈ Ioc M (M + N), LeanLab.PNTPort.LargeSieve.e (n * (α r - α r'))).re) ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [Complex.re_sum] using
      (Complex.re_le_norm _).trans
        (offdiagonal_bound_of_hilbert s α hδ hs
          (fun v => circular_hilbert_of_cosecant s α hδ v
            (LeanLab.Linnik.HilbertCosecant.cosecant_hilbert s α hδ hs v)) b M N)
  calc
    _ ≤ (N : ℝ) * (∑ r ∈ s, ‖b r‖ ^ 2) + (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 :=
      add_le_add le_rfl hre
    _ = _ := by ring

/-- The Farey sum regrouped by denominator. -/
private lemma farey_sum_eq' (Q : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ x ∈ LeanLab.PNTPort.LargeSieve.farey Q, F x
      = ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), F (q, c) := by
  unfold LeanLab.PNTPort.LargeSieve.farey
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun q hq => ?_
  rw [mem_Icc] at hq
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩

/-- Farey spacing turns the sharp dual constant into `N + Q²`. -/
private lemma farey_sampling_sharp (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), a n *
        LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp only [show Icc 1 (0 : ℕ) = ∅ by decide, sum_empty,
      Nat.cast_zero, zero_pow, add_zero]
    positivity
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  have hI : Ioc (M : ℤ) ((M : ℤ) + N) = (Ioc M (M + N)).map emb := by
    ext z
    simp only [Finset.mem_Ioc, Finset.mem_map, emb, Function.Embedding.coeFn_mk,
      Int.ofNat_eq_natCast]
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨z.toNat, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
      constructor <;> omega
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hbound := spaced_sampling_sharp
    (LeanLab.PNTPort.LargeSieve.farey Q) LeanLab.PNTPort.LargeSieve.fareyPt
    hδ (LeanLab.PNTPort.LargeSieve.farey_spaced Q)
    (fun z : ℤ => a z.toNat) (M : ℤ) N
  rw [hI] at hbound
  simp only [sum_map, emb, Function.Embedding.coeFn_mk,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast] at hbound
  have hconst : (1 : ℝ) / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by simp
  rw [hconst] at hbound
  rw [farey_sum_eq'] at hbound
  simpa only [LeanLab.PNTPort.LargeSieve.fareyPt, Nat.coprime_comm] using hbound

/-- The sharp additive large sieve at Farey fractions (Selberg; Montgomery 1971). -/
private lemma additive_large_sieve_sharp (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 :=
  farey_sampling_sharp a M N Q

/-- Character orthogonality reduces the multiplicative sieve to additive sums. -/
private lemma primitive_sieve_le_additive (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N),
        (starRingEnd ℂ) (a n) * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 := by
  classical
  apply sum_le_sum
  intro q hq
  letI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  let I : Finset ℤ := (Ioc M (M + N)).map emb
  let az : ℤ → ℂ := fun z => a z.toNat
  have h := LeanLab.PNTPort.LargeSieve.prim_chars_le I az (q := q)
  simpa only [I, az, sum_map, emb, Function.Embedding.coeFn_mk,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast, Int.cast_ofNat] using h

/-- The sharp multiplicative large sieve over primitive characters. -/
private lemma char_large_sieve (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  calc
    _ ≤ _ := primitive_sieve_le_additive a M N Q
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ Ioc M (M + N), ‖(starRingEnd ℂ) (a n)‖ ^ 2 :=
      additive_large_sieve_sharp (fun n => (starRingEnd ℂ) (a n)) M N Q
    _ = _ := by simp only [Complex.norm_conj]

/-- LEAF. Journal p. 1225 display 15, the first large sieve moment.
Apply Iwaniec and Kowalski Theorem 7.13 to the coefficients restricted by n coprime to s.
This is one quadratic factor, not the bilinear block estimate. -/
theorem coefficient_energy (c : ℕ → ℂ) (X R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hR : 1 ≤ R) :
    blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c ≤
      (X + 4 * R ^ 2) * X := by
  classical
  set M0 : ℕ := ⌈X⌉₊ with hM0
  set Q : ℕ := ⌈2 * R⌉₊ - 1 with hQ
  set Sv : Finset ℕ := (nRange X).filter (fun n => Nat.Coprime n s) with hSv
  set a : ℕ → ℂ := fun n => if n ∈ Sv then c n else 0 with ha
  have hM0pos : 1 ≤ M0 := by
    rw [hM0]
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
  set n0 : ℕ := M0 - 1 with hn0
  have hn0M : n0 + 1 = M0 := by omega
  have hSsub : Sv ⊆ Ioc 0 n0 := by
    intro n hn
    rw [hSv, mem_filter, nRange, mem_Ico] at hn
    rw [mem_Ioc]
    omega
  have hper : ∀ (r : ℕ) (χ : DirichletCharacter ℂ r),
      (∑ n ∈ Sv, c n * χ n) = ∑ n ∈ Ioc 0 n0, a n * χ n := by
    intro r χ
    have h1 : ∀ n ∈ Sv, a n * χ n = c n * χ n := by
      intro n hn
      simp only [ha, if_pos hn]
    rw [← Finset.sum_congr rfl h1]
    exact Finset.sum_subset hSsub (fun x _ hx => by simp [ha, hx])
  have hsub : blockModuli R ⊆ Icc 1 Q := by
    intro r hr
    rw [blockModuli, mem_filter, mem_Ico] at hr
    rw [mem_Icc]
    refine ⟨by omega, ?_⟩
    have hlt : r < ⌈2 * R⌉₊ := hr.1.2
    have hpos : 1 ≤ ⌈2 * R⌉₊ := by
      have : (0 : ℝ) < 2 * R := by linarith
      exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 this).ne'
    rw [hQ]
    omega
  have hpt : ∀ r : ℕ, (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
      (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ n ∈ Sv, c n * χ n‖ ^ 2)
      = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
          ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc 0 n0, a n * χ n‖ ^ 2 := by
    intro r
    apply sum_congr rfl
    intro χ _
    rw [hper r χ]
  have hE : blockEnergy R Sv c = ∑ r ∈ blockModuli R,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
        ((r : ℝ) / r.totient) * ‖∑ n ∈ Sv, c n * χ n‖ ^ 2 := by
    rw [blockEnergy, blockCharacters, sum_sigma]
  have hblock : (∑ r ∈ blockModuli R,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
        ((r : ℝ) / r.totient) * ‖∑ n ∈ Sv, c n * χ n‖ ^ 2) ≤
      ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Ioc 0 n0, a n * χ n‖ ^ 2 := by
    have h1 : (∑ r ∈ blockModuli R,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
          ((r : ℝ) / r.totient) * ‖∑ n ∈ Sv, c n * χ n‖ ^ 2)
        = ∑ r ∈ blockModuli R,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
            ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc 0 n0, a n * χ n‖ ^ 2 :=
      sum_congr rfl (fun r _ => hpt r)
    rw [h1]
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ =>
      sum_nonneg (fun χ _ => by positivity))).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro r _
    rw [mul_sum]
  have hA : ∑ n ∈ Ioc 0 n0, ‖a n‖ ^ 2 ≤ (n0 : ℝ) := by
    have hAeq : ∑ n ∈ Ioc 0 n0, ‖a n‖ ^ 2 = ∑ n ∈ Sv, ‖c n‖ ^ 2 := by
      have hsub' : ∑ n ∈ Sv, ‖a n‖ ^ 2 = ∑ n ∈ Ioc 0 n0, ‖a n‖ ^ 2 :=
        Finset.sum_subset hSsub (fun x _ hx => by simp [ha, hx])
      rw [← hsub']
      exact Finset.sum_congr rfl (fun n hn => by simp [ha, hn])
    have hc1 : ∑ n ∈ Sv, ‖c n‖ ^ 2 ≤ ∑ n ∈ Sv, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      have h := hc n
      have h0 := norm_nonneg (c n)
      nlinarith
    have hcard : Sv.card ≤ n0 := by
      have h1 : Sv.card ≤ (nRange X).card := card_le_card (filter_subset _ _)
      have h2 : (nRange X).card = n0 := by
        rw [nRange, Nat.card_Ico, ← hM0, hn0]
      omega
    calc ∑ n ∈ Ioc 0 n0, ‖a n‖ ^ 2 = ∑ n ∈ Sv, ‖c n‖ ^ 2 := hAeq
      _ ≤ ∑ n ∈ Sv, (1 : ℝ) := hc1
      _ = (Sv.card : ℝ) := by simp
      _ ≤ (n0 : ℝ) := by exact_mod_cast hcard
  have hn0le : (n0 : ℝ) ≤ X := by
    have h1 : (M0 : ℝ) < X + 1 := by
      rw [hM0]
      exact Nat.ceil_lt_add_one (by linarith)
    have h2 : (n0 : ℝ) = (M0 : ℝ) - 1 := by
      rw [hn0, Nat.cast_sub hM0pos]
      push_cast
      ring
    linarith
  have hQlt : (Q : ℝ) < 2 * R := by
    have hpos : 1 ≤ ⌈2 * R⌉₊ := by
      have : (0 : ℝ) < 2 * R := by linarith
      exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 this).ne'
    have h1 : (Q : ℝ) = (⌈2 * R⌉₊ : ℝ) - 1 := by
      rw [hQ, Nat.cast_sub hpos]
      push_cast
      ring
    have h2 : (⌈2 * R⌉₊ : ℝ) < 2 * R + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hQ2 : (Q : ℝ) ^ 2 ≤ 4 * R ^ 2 := by
    have h0 : (0 : ℝ) ≤ Q := by positivity
    nlinarith [hQlt]
  have hsieve := char_large_sieve a 0 n0 Q
  simp only [Nat.zero_add] at hsieve
  have hnon : (0 : ℝ) ≤ (n0 : ℝ) + (Q : ℝ) ^ 2 := by positivity
  calc blockEnergy R Sv c
      = ∑ r ∈ blockModuli R,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
            ((r : ℝ) / r.totient) * ‖∑ n ∈ Sv, c n * χ n‖ ^ 2 := hE
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Ioc 0 n0, a n * χ n‖ ^ 2 := hblock
    _ ≤ ((n0 : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc 0 n0, ‖a n‖ ^ 2 := hsieve
    _ ≤ ((n0 : ℝ) + (Q : ℝ) ^ 2) * n0 := mul_le_mul_of_nonneg_left hA hnon
    _ ≤ (X + 4 * R ^ 2) * X := by nlinarith [hn0le, hQ2, Nat.cast_nonneg (α := ℝ) n0]


/-! ### Private helpers for `prime_energy`

The second large-sieve moment is the lab's `multiplicative_large_sieve` (constant `N + 2Q²`)
applied to the indicator of the primes `Z ≤ p < ⌈Y⌉`. The exact constant `N + Q²` is not
available, so the factor two is recovered from the elementary fact that every prime counted
is at least `25`, hence odd: at most half of the integers up to `⌈Y⌉` are counted. -/

/-- The canonical inclusion `P ⊆ ℤ` agrees with the `Ioc` interval index set. -/
private lemma transfer_set (P : Finset ℕ) (m : ℕ) (hpos : ∀ p ∈ P, 0 < p)
    (hlt : ∀ p ∈ P, p < m) :
    (Ioc (0:ℤ) (0 + (m : ℕ))).filter (fun n => (n.toNat : ℕ) ∈ P)
      = P.image (fun p : ℕ => (p : ℤ)) := by
  ext n
  simp only [mem_filter, mem_Ioc, mem_image]
  constructor
  · rintro ⟨⟨hn0, hnm⟩, hp⟩
    exact ⟨n.toNat, hp, Int.toNat_of_nonneg (le_of_lt hn0)⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, by simpa using hp⟩
    · exact_mod_cast hpos p hp
    · have := hlt p hp
      push_cast
      omega

/-- `χ` applied to a nonnegative integer through `ℤ` or through `ℕ` agree. -/
private lemma char_cast (r : ℕ) (χ : DirichletCharacter ℂ r) (n : ℤ) (hn : 0 ≤ n) :
    χ ((n.toNat : ℕ)) = χ n := by
  have h : ((n.toNat : ℕ) : ZMod r) = (n : ZMod r) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
  exact congrArg χ h

/-- The interval sum of the indicator of `P` is the character sum over `P`. -/
private lemma sum_transfer (P : Finset ℕ) (m : ℕ) (hpos : ∀ p ∈ P, 0 < p)
    (hlt : ∀ p ∈ P, p < m) (r : ℕ) (χ : DirichletCharacter ℂ r) :
    (∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
        (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n) = ∑ p ∈ P, χ p := by
  have h1 : ∀ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
      (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n
        = if ((n.toNat : ℕ) ∈ P) then χ n.toNat else 0 := by
    intro n hn
    rw [ite_mul, one_mul, zero_mul]
    split_ifs with h
    · rw [char_cast r χ n (le_of_lt (mem_Ioc.mp hn).1)]
    · rfl
  rw [sum_congr rfl h1, ← sum_filter, transfer_set P m hpos hlt]
  have hinj : Set.InjOn (fun p : ℕ => (p : ℤ)) (↑P) := fun a _ b _ h => by simpa using h
  rw [Finset.sum_image (f := fun n : ℤ => χ n.toNat) (g := fun p : ℕ => (p : ℤ)) hinj]
  push_cast
  rfl

/-- The squared norms of the indicator sum to the cardinality of `P`. -/
private lemma sum_norm_sq_indicator (P : Finset ℕ) (m : ℕ) (hpos : ∀ p ∈ P, 0 < p)
    (hlt : ∀ p ∈ P, p < m) :
    (∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)), ‖(if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0)‖ ^ 2)
      = (P.card : ℝ) := by
  have h1 : ∀ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
      ‖(if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0)‖ ^ 2
        = if ((n.toNat : ℕ) ∈ P) then (1:ℝ) else 0 := by
    intro n hn
    split_ifs with h <;> simp
  rw [sum_congr rfl h1, ← sum_filter, transfer_set P m hpos hlt]
  rw [sum_const, card_image_of_injective _ (fun a b h => by simpa using h), nsmul_eq_mul, mul_one]

/-- A prime `p ≥ 25` is odd. -/
private lemma odd_of_prime_ge (p : ℕ) (Z : ℝ) (hp : p.Prime) (hZ : 25 ≤ Z)
    (hge : Z ≤ (p : ℝ)) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    norm_num at hge
    linarith
  · exact h

/-- Primes `25 ≤ Z ≤ p < ⌈Y⌉` are at most half of the integers up to `Y`. -/
private lemma prime_card_le (P : Finset ℕ) (Y Z : ℝ) (m : ℕ) (hm : m = ⌈Y⌉₊)
    (hY : 25 ≤ Y) (hZ : 25 ≤ Z) (hprime : ∀ p ∈ P, p.Prime) (hge : ∀ p ∈ P, Z ≤ (p:ℝ))
    (hlt : ∀ p ∈ P, p < m) : (P.card : ℝ) ≤ Y / 2 := by
  have hmY : (m : ℝ) ≤ Y + 1 := by
    rw [hm]; exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hsub : P ⊆ (Ico 12 ((m - 2) / 2 + 1)).image (fun k => 2 * k + 1) := by
    intro p hp
    have hodd := odd_of_prime_ge p Z (hprime p hp) hZ (hge p hp)
    have h25 : 25 ≤ p := by
      have h' : (25:ℝ) ≤ (p:ℝ) := le_trans hZ (hge p hp)
      exact_mod_cast h'
    have hpm : p < m := hlt p hp
    rw [mem_image]
    refine ⟨(p - 1) / 2, ?_, ?_⟩
    · rw [mem_Ico]
      omega
    · omega
  have hcard : P.card ≤ ((m - 2) / 2 + 1) - 12 := by
    refine (card_le_card hsub).trans ?_
    rw [card_image_of_injective _ (fun a b h => by omega), Nat.card_Ico]
  have hmhalf : (((m - 2) / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
    have h1 : ((m - 2) / 2 : ℕ) ≤ m / 2 := Nat.div_le_div_right (by omega)
    have h2 : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      exact_mod_cast Nat.div_mul_le_self m 2
    exact le_trans (by exact_mod_cast h1) h2
  rcases Nat.lt_or_ge ((m - 2) / 2 + 1) 12 with h | h
  · have hz : ((m - 2) / 2 + 1) - 12 = 0 := by omega
    rw [hz] at hcard
    have hP0 : P.card = 0 := by omega
    rw [hP0]
    push_cast
    linarith
  · have hstep : ((((m - 2) / 2 + 1) - 12 : ℕ) : ℝ) = ((m - 2) / 2 : ℕ) - 11 := by
      have he : (((m - 2) / 2 + 1) - 12 : ℕ) = (m - 2) / 2 - 11 := by omega
      rw [he, Nat.cast_sub (by omega)]
      push_cast
      ring
    have hcard' : (P.card : ℝ) ≤ ((m - 2) / 2 : ℕ) - 11 := by
      calc (P.card : ℝ) ≤ ((((m - 2) / 2 + 1) - 12 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = ((m - 2) / 2 : ℕ) - 11 := hstep
    have hm2 : (m : ℝ) / 2 ≤ (Y + 1) / 2 := by linarith
    linarith

/-- The block energy, read as a double sum, is dominated by the lab's multiplicative
large-sieve sum over moduli `≤ Q`. -/
private lemma block_energy_le_ls (P : Finset ℕ) (m Mr Q : ℕ) (R : ℝ) (hQ : Q + 1 = Mr)
    (hMr : Mr = ⌈2 * R⌉₊) (hpos : ∀ p ∈ P, 0 < p) (hlt : ∀ p ∈ P, p < m) :
    (∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2)
      ≤ ∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
  have hsub : blockModuli R ⊆ Ico 1 Mr := by
    intro r hr
    rw [blockModuli, mem_filter, mem_Ico] at hr
    rw [mem_Ico]
    rw [hMr]
    omega
  have hpt : ∀ r : ℕ, (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2)
      = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
          ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
            (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
    intro r
    apply sum_congr rfl
    intro χ hχ
    rw [sum_transfer P m hpos hlt r χ]
  calc (∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2)
      = ∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive),
            ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 :=
        sum_congr rfl (fun r _ => hpt r)
    _ ≤ ∑ r ∈ Ico 1 Mr, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive),
            ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => ?_)
        apply sum_nonneg
        intro χ _
        positivity
    _ = ∑ r ∈ Ico 1 Mr, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2 := by
        apply sum_congr rfl
        intro r _
        exact (hpt r).symm
    _ = ∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
        rw [← hQ, Finset.sum_Ico_eq_sum_range]
        apply sum_congr rfl
        intro k _
        rw [show 1 + k = k + 1 by omega, hpt, mul_sum]

/-- LEAF. Journal p. 1225 display 15, the second large sieve moment.
Apply Iwaniec and Kowalski Theorem 7.13 to the prime indicator with p not dividing s.
This factor has no arbitrary coefficient sequence. -/
theorem prime_energy (Y Z R : ℝ) (s : ℕ)
    (hY : 25 ≤ Y) (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) ≤
      (Y + 4 * R ^ 2) * Y := by
  set P : Finset ℕ := (pRange Y Z).filter (fun p => ¬ p ∣ s) with hPdef
  set m : ℕ := ⌈Y⌉₊ with hmdef
  set Mr : ℕ := ⌈2 * R⌉₊ with hMrdef
  set Q : ℕ := Mr - 1 with hQdef
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  -- membership facts for the prime block
  have hmem : ∀ p ∈ P, p ∈ range m ∧ p.Prime ∧ Z ≤ (p : ℝ) := by
    intro p hp
    rw [hPdef, mem_filter, pRange, mem_filter, mem_range] at hp
    exact ⟨by rw [hmdef]; exact mem_range.mpr hp.1.1, hp.1.2.1, hp.1.2.2⟩
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (hmem p hp).2.1
  have hge : ∀ p ∈ P, Z ≤ (p : ℝ) := fun p hp => (hmem p hp).2.2
  have hltP : ∀ p ∈ P, p < m := fun p hp => mem_range.mp (hmem p hp).1
  have hposP : ∀ p ∈ P, 0 < p := fun p hp => (hprime p hp).pos
  -- ceiling arithmetic
  have hmMr : 2 ≤ Mr := by
    have h2R : (2:ℝ) ≤ 2 * R := by linarith
    have : (2:ℕ) ≤ ⌈2 * R⌉₊ := by
      have h' : (2:ℝ) ≤ (⌈2 * R⌉₊ : ℝ) := le_trans h2R (Nat.le_ceil (2 * R))
      exact_mod_cast h'
    rw [hMrdef]; exact this
  have hQ1 : 1 ≤ Q := by omega
  have hQsucc : Q + 1 = Mr := by omega
  have hQcast : (Q : ℝ) = (Mr : ℝ) - 1 := by
    rw [hQdef, Nat.cast_sub (show 1 ≤ Mr by omega)]
    push_cast
    ring
  have hMrlt : (Mr : ℝ) < 2 * R + 1 := Nat.ceil_lt_add_one (by linarith)
  have hQlt : (Q : ℝ) < 2 * R := by rw [hQcast]; linarith
  -- the two moments
  have hEQ : blockEnergy R P (fun _ => 1)
      = ∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2 := by
    rw [blockEnergy, blockCharacters, sum_sigma]
    simp only [one_mul]
  have hstep := block_energy_le_ls P m Mr Q R hQsucc hMrdef hposP hltP
  have hLS := LeanLab.PNTPort.LargeSieve.multiplicative_large_sieve (Q := Q) hQ1
    (fun n : ℤ => if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) 0 m
  have hcard := sum_norm_sq_indicator P m hposP hltP
  have hpc := prime_card_le P Y Z m hmdef hY hZ hprime hge hltP
  rw [hEQ]
  refine hstep.trans ?_
  refine hLS.trans ?_
  rw [hcard]
  -- final constant comparison
  have hmY : (m : ℝ) ≤ 2 * Y := by
    have : (m : ℝ) ≤ Y + 1 := by
      rw [hmdef]; exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
    linarith
  have hP0 : (0:ℝ) ≤ (P.card : ℝ) := by positivity
  have hA0 : (0:ℝ) ≤ (m : ℝ) + 2 * (Q : ℝ) ^ 2 := by positivity
  have hA : (m : ℝ) + 2 * (Q : ℝ) ^ 2 ≤ 2 * Y + 8 * R ^ 2 := by
    have hsq : (Q : ℝ) ^ 2 < (2 * R) ^ 2 := by
      have := hQlt
      nlinarith [hR0]
    nlinarith
  have hB0 : (0:ℝ) ≤ 2 * Y + 8 * R ^ 2 := by positivity
  have hmul := mul_le_mul hA hpc hP0 hB0
  nlinarith [hmul]

/-- Weighted Cauchy Schwarz before the two analytic moments, journal display 15. -/
theorem block_cauchy (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ) (hR : 1 ≤ R) :
    (∑ r ∈ blockModuli R, (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √(blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c *
        blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1)) / R := by
  let f : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    ‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * i.2 n‖
  let g : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), i.2 p‖
  let w : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    (i.1 : ℝ) / i.1.totient
  have hRp : 0 < R := by linarith
  have hcs := LeanLab.PNTPort.LargeSieve.cs_weighted (blockCharacters R) w f g
    (fun _ _ => by dsimp [w]; positivity)
  have hsq : (∑ i ∈ blockCharacters R, w i * (f i * g i)) ^ 2 ≤
      blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c *
        blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) := by
    simpa only [blockEnergy, w, f, g, one_mul] using hcs
  have hroot := Real.le_sqrt_of_sq_le hsq
  apply le_trans _ (div_le_div_of_nonneg_right hroot hRp.le)
  rw [sum_div]
  change _ ≤ ∑ i ∈ (blockModuli R).sigma (fun r =>
      (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive)),
      w i * (f i * g i) / R
  rw [sum_sigma]
  apply sum_le_sum
  intro r hr
  rw [primitiveTerm, mul_sum]
  apply sum_le_sum
  intro χ hχ
  change (r.totient : ℝ)⁻¹ * (_ * _) ≤
    ((r : ℝ) / r.totient) * (_ * _) / R
  have hrr : R ≤ (r : ℝ) := (mem_filter.mp hr).2
  have hφ : (0 : ℝ) ≤ (r.totient : ℝ)⁻¹ := by positivity
  have hweight : (r.totient : ℝ)⁻¹ ≤ ((r : ℝ) / r.totient) / R := by
    apply (le_div_iff₀ hRp).mpr
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hrr hφ
  simpa only [div_mul_eq_mul_div] using
    mul_le_mul_of_nonneg_right hweight (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Exact statement of Decomp148c.dyadic_block, assembled from the two separate moments.
CONDITIONAL ON coefficient_energy and prime_energy. No direct sorry. -/
theorem dyadic_block (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    (∑ r ∈ (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R := by
  apply (block_cauchy c X Y Z R s hR).trans
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply Real.sqrt_le_sqrt
  have ha := coefficient_energy c X R s hc hX hR
  have hb := prime_energy Y Z R s hY hZ hZY hR
  have hnon : 0 ≤ blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) := by
    unfold blockEnergy
    exact sum_nonneg (fun _ _ => by positivity)
  have hx : 0 ≤ (X + 4 * R ^ 2) * X := by positivity
  convert mul_le_mul ha hb hnon hx using 1 <;> ring

end
end LeanLab.BS2022GRH.Decomp374a

#print axioms LeanLab.BS2022GRH.Decomp374a.coefficient_energy
#print axioms LeanLab.BS2022GRH.Decomp374a.prime_energy
#print axioms LeanLab.BS2022GRH.Decomp374a.block_cauchy
#print axioms LeanLab.BS2022GRH.Decomp374a.dyadic_block
