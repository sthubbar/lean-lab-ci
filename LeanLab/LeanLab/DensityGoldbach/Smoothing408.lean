/-
Single function Bohr smoothing, adapted from the existing U1467 proof.
Source: Shao 1206.6139v2 page 14 Lemma 4.2 and Green and Tao
math/0405581v2 pages 16 to 18, displays 5.8 to 5.15.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.U1467Bohr
import LeanLab.DensityGoldbach.Fourier408

open Finset
open scoped Classical

namespace LeanLab.DensityGoldbach.Smoothing408
open LeanLab.DensityGoldbach.U1446 LeanLab.DensityGoldbach.U1467

/-- Shao page 14 Lemma 4.2 in expectation normalization, for one function.
The unused binary mean hypothesis of the existing U1467 construction is removed.
All kernel and Bohr size lemmas are reused. -/
theorem normalized_smoothing (a ε p M : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hp : 2 < p) (hM : 0 < M) :
    ∃ η : ℝ, 0 < η ∧ ∀ N : ℕ, ∀ [NeZero N], N.Prime →
      ∀ f ν : ZMod N → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ ν x) → lpHat N p f ≤ M →
      (∀ r, ‖hatE N ν r - (if r = 0 then 1 else 0)‖ ≤ η) →
      ∃ g : ZMod N → ℝ, (∀ x, 0 ≤ g x ∧ g x ≤ 1 + a) ∧
        avg N g = avg N f ∧ (∀ r, ‖hatE N f r - hatE N g r‖ ≤ ε) ∧ lpHat N p g ≤ M := by
  have HB := bohrLower_proved
  set ε' := min (ε / 4) (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hε'4 : ε' ≤ ε / 4 := min_le_left _ _
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hp0 : 0 < p := by linarith
  set k := ⌊M ^ p / ε' ^ p⌋₊ with hk
  obtain ⟨κ, hκ, hBohr⟩ := HB ε' hε'0 k
  refine ⟨min 1 (a * κ), lt_min one_pos (by positivity), ?_⟩
  intro N inst hNp f ν hf hl hν
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  -- large spectra
  have hspec : ∀ f : ZMod N → ℝ, lpHat N p f ≤ M →
      (univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖)).card ≤ k := by
    intro f hf
    apply Nat.le_floor
    have hS := sum_pow_le f p M hp0 hf
    have hR : ((univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖)).card : ℝ) * ε' ^ p ≤
        ∑ r : ZMod N, ‖hatE N f r‖ ^ p := by
      calc ((univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖)).card : ℝ) * ε' ^ p
          = ∑ r ∈ univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖), ε' ^ p := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ r ∈ univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖), ‖hatE N f r‖ ^ p :=
            Finset.sum_le_sum fun r hr =>
              Real.rpow_le_rpow hε'0.le (mem_filter.1 hr).2 hp0.le
        _ ≤ ∑ r : ZMod N, ‖hatE N f r‖ ^ p :=
            Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              fun r _ _ => Real.rpow_nonneg (norm_nonneg _) _
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hε'0 p)]
    linarith
  set R := univ.filter (fun r : ZMod N => ε' ≤ ‖hatE N f r‖) with hR
  have hRk : R.card ≤ k := hspec f hl
  set B := univ.filter (fun x : ZMod N => ∀ r ∈ R, ‖(ZMod.stdAddChar (r * x) : ℂ) - 1‖ ≤ ε')
    with hBdef
  have hBsize : κ * N ≤ B.card := hBohr N R hRk
  have hBpos : (0 : ℝ) < B.card := lt_of_lt_of_le (by positivity) hBsize
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hBpos
  have hNB : (N : ℝ) / B.card ≤ 1 / κ := by
    rw [div_le_div_iff₀ hBpos hκ]; linarith
  set K := kerB B
  have hK0 := kerB_nonneg B
  set kk : ZMod N → ℝ := fun r => ‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2 with hkk
  have hkk0 : ∀ r, 0 ≤ kk r := fun r => by positivity
  have hkk1 : ∀ r, kk r ≤ 1 := kerB_hat_le_one B hB
  have hKhat : ∀ r, hatE N K r = (kk r : ℂ) := hatE_kerB B
  have hkk_zero : kk 0 = 1 := by
    have h := (hatE_zero N K).symm.trans (hKhat 0)
    -- avg K = 1 from `Σ_r K̂ e(0)`: compute directly instead
    have hS0 : sB B 0 = B.card := by simp [sB]
    simp only [kk, hS0, Complex.norm_natCast]
    field_simp
  -- averages of `ν_i`
  have havgν : ∀ ν : ZMod N → ℝ, (∀ r, ‖hatE N ν r - (if r = 0 then 1 else 0)‖ ≤
      min 1 (a * κ)) → avg N ν ≤ 2 := by
    intro ν hν
    have := hν 0
    rw [if_pos rfl, hatE_zero] at this
    rw [show ((avg N ν : ℂ) - 1) = ((avg N ν - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at this
    have := (le_abs_self _).trans this
    linarith [min_le_left 1 (a * κ)]
  -- the construction for one function
  have build : ∀ f ν : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ ν n) → lpHat N p f ≤ M →
      (∀ r, ‖hatE N ν r - (if r = 0 then 1 else 0)‖ ≤ min 1 (a * κ)) →
      (∀ r, ε' ≤ ‖hatE N f r‖ → r ∈ R) →
      (∀ n, 0 ≤ convE N f K n ∧ convE N f K n ≤ 1 + a) ∧
      avg N (convE N f K) = avg N f ∧ (∀ r, ‖hatE N f r - hatE N (convE N f K) r‖ ≤ ε) ∧
      lpHat N p (convE N f K) ≤ M := by
    intro f ν hf hl hν hfR
    have hghat : ∀ r, hatE N (convE N f K) r = hatE N f r * (kk r : ℂ) := fun r => by
      rw [hatE_conv, hKhat]
    have hfavg : avg N f ≤ 2 := (avg_mono _ _ fun n => (hf n).2).trans (havgν ν hν)
    refine ⟨fun n => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · unfold convE
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => mul_nonneg (hf m).1 (hK0 _))
    · -- `f * K ≤ ν * K ≤ 1 + c N/|B|`
      have hle : convE N f K n ≤ convE N ν K n := by
        unfold convE
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_right (hf m).2 (hK0 _)) (by positivity)
      refine hle.trans ?_
      have hinv := conv_inv ν K n
      have hsplit : ∑ r : ZMod N, hatE N ν r * hatE N K r * ZMod.stdAddChar (r * n) =
          ∑ r : ZMod N, (hatE N ν r - (if r = 0 then 1 else 0)) * (kk r : ℂ) *
            ZMod.stdAddChar (r * n) + 1 := by
        have : ∑ r : ZMod N, (if r = 0 then (1 : ℂ) else 0) * (kk r : ℂ) *
            ZMod.stdAddChar (r * n) = 1 := by
          rw [Finset.sum_eq_single 0]
          · simp [hkk_zero]
          · intro r _ hr; simp [hr]
          · simp
        have hs2 : ∑ r : ZMod N, hatE N ν r * hatE N K r * ZMod.stdAddChar (r * n) =
            ∑ r : ZMod N, ((hatE N ν r - (if r = 0 then 1 else 0)) * (kk r : ℂ) *
              ZMod.stdAddChar (r * n) + (if r = 0 then (1 : ℂ) else 0) * (kk r : ℂ) *
              ZMod.stdAddChar (r * n)) :=
          Finset.sum_congr rfl fun r _ => by rw [hKhat]; ring
        rw [hs2, Finset.sum_add_distrib, this]
      rw [hsplit] at hinv
      have hnorm : ‖∑ r : ZMod N, (hatE N ν r - (if r = 0 then 1 else 0)) * (kk r : ℂ) *
          ZMod.stdAddChar (r * n)‖ ≤ a * κ * (N / B.card) := by
        refine (norm_sum_le _ _).trans ?_
        rw [← sum_hat_kerB B hB, Finset.mul_sum]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hkk0 r)]
        exact mul_le_mul_of_nonneg_right ((hν r).trans (min_le_right _ _)) (hkk0 r)
      have hre : convE N ν K n ≤ ‖((convE N ν K n : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
      rw [hinv] at hre
      have h3 := (hre.trans (norm_add_le _ _)).trans (add_le_add hnorm (le_of_eq norm_one))
      have h4 : a * κ * (N / B.card) ≤ a := by
        calc a * κ * (N / B.card) ≤ a * κ * (1 / κ) :=
              mul_le_mul_of_nonneg_left hNB (by positivity)
          _ = a := by field_simp
      linarith
    · have h := hghat 0
      rw [hatE_zero, hatE_zero, hkk_zero] at h
      push_cast at h
      exact_mod_cast (by simpa using h)
    · intro r
      rw [hghat, show hatE N f r - hatE N f r * (kk r : ℂ) = hatE N f r * ((1 - kk r : ℝ) : ℂ) by
        push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hkk1 r])]
      have hfr : ‖hatE N f r‖ ≤ 2 := (norm_hatE_le f (fun n => (hf n).1) r).trans hfavg
      by_cases hr : ε' ≤ ‖hatE N f r‖
      · have hrR := hfR r hr
        have hge := hat_kerB_ge B hB r ε' (by linarith)
          (fun b hb => (mem_filter.1 hb).2 r hrR)
        have : 1 - kk r ≤ 2 * ε' := by simp only [kk]; nlinarith
        calc ‖hatE N f r‖ * (1 - kk r) ≤ 2 * (2 * ε') :=
              mul_le_mul hfr this (by linarith [hkk1 r]) (by norm_num)
          _ ≤ ε := by linarith
      · push Not at hr
        calc ‖hatE N f r‖ * (1 - kk r) ≤ ε' * 1 :=
              mul_le_mul hr.le (by linarith [hkk0 r]) (by linarith [hkk1 r]) hε'0.le
          _ ≤ ε := by linarith
    · refine le_trans ?_ hl
      unfold lpHat
      apply Real.rpow_le_rpow (Finset.sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _)
        _ (by positivity)
      refine Finset.sum_le_sum fun r _ => Real.rpow_le_rpow (norm_nonneg _) ?_ hp0.le
      rw [hghat, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hkk0 r)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hkk1 r)
  obtain ⟨h1, h2, h3, h4⟩ := build f ν hf hl hν
    (fun r hr => mem_filter.mpr ⟨mem_univ _, hr⟩)
  exact ⟨convE N f K, h1, h2, h3, h4⟩

/-- Shao page 14 Lemma 4.2 part 4, the residual q norm bound.
The Bohr kernel multiplier lies between zero and one, so subtraction
also contracts every positive Fourier q norm. -/
theorem residual_norm {N : ℕ} [NeZero N] (B : Finset (ZMod N)) (hB : B.Nonempty)
    (f : ZMod N → ℝ) (q : ℝ) (hq : 0 < q) :
    lpHat N q (fun x => f x - convE N f (kerB B) x) ≤ lpHat N q f := by
  unfold lpHat
  apply Real.rpow_le_rpow (sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _) _
    (by positivity)
  apply sum_le_sum
  intro r _
  apply Real.rpow_le_rpow (norm_nonneg _) _ hq.le
  have hsub : hatE N (fun x => f x - convE N f (kerB B) x) r =
      hatE N f r - hatE N (convE N f (kerB B)) r := by
    simp only [hatE, Complex.ofReal_sub, sub_mul, sum_sub_distrib, mul_sub]
  rw [hsub, hatE_conv, hatE_kerB]
  let k : ℝ := ‖sB B r‖ ^ 2 / (B.card : ℝ) ^ 2
  have hk0 : 0 ≤ k := by positivity
  have hk1 : k ≤ 1 := kerB_hat_le_one B hB r
  change ‖hatE N f r - hatE N f r * (k : ℂ)‖ ≤ ‖hatE N f r‖
  have hid : hatE N f r - hatE N f r * (k : ℂ) =
      hatE N f r * ((1 - k : ℝ) : ℂ) := by push_cast; ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact mul_le_of_le_one_right (norm_nonneg _) (by linarith)

/-- Shao page 13 Fourier convention. Scaling a probability weight by N
converts it to the lab's expectation normalization, with a frequency sign change. -/
theorem scaled_transform {N : ℕ} [NeZero N] (f : ZMod N → ℝ) (r : ZMod N) :
    hatE N (fun x => (N : ℝ) * f x) r = fourierZN N f (-r) := by
  rw [hatE, Fourier408.fourier_character]
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  rw [neg_mul]
  field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N]

/-- Shao page 13 Fourier convention, reversing the normalization change. -/
theorem probability_transform {N : ℕ} [NeZero N] (g : ZMod N → ℝ) (r : ZMod N) :
    fourierZN N (fun x => g x / N) r = hatE N g (-r) := by
  rw [hatE, Fourier408.fourier_character, mul_sum]
  push_cast
  apply sum_congr rfl
  intro n _
  simp only [neg_mul, neg_neg]
  ring

/-- Shao page 14 Lemma 4.2. Fourier q norms agree under probability
normalization and scaling because negation permutes the frequencies. -/
theorem scaled_norm {N : ℕ} [NeZero N] (f : ZMod N → ℝ) (q : ℝ) :
    lpHat N q (fun x => (N : ℝ) * f x) =
      (∑ r : ZMod N, ‖fourierZN N f r‖ ^ q) ^ (1 / q) := by
  unfold lpHat
  simp_rw [scaled_transform]
  congr 1
  exact Equiv.sum_comp (Equiv.neg _) (fun r => ‖fourierZN N f r‖ ^ q)

/-- Shao page 14 Lemma 4.2 in the sealed probability normalization.
Only the Bohr construction is used. There is no mean or density hypothesis. -/
theorem probability_smoothing (a ε q M : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hq2 : 2 < q) (hq3 : q < 3) (hM : 0 < M) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N.Prime → N₀ ≤ N → ∀ [NeZero N],
      ∀ ν f : ZMod N → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ ν x) →
      (∀ r, ‖fourierZN N ν r - (if r = 0 then 1 else 0)‖ ≤ η) →
      (∑ r, ‖fourierZN N f r‖ ^ q) ^ (1 / q) ≤ M →
      ∃ g : ZMod N → ℝ,
        (∀ x, 0 ≤ g x ∧ g x ≤ (1 + a) / N) ∧
        (∑ x, g x) = ∑ x, f x ∧
        (∀ r, ‖fourierZN N f r - fourierZN N g r‖ ≤ ε) ∧
        (∑ r, ‖fourierZN N g r‖ ^ q) ^ (1 / q) ≤ M := by
  obtain ⟨η, hη, hSmooth⟩ := normalized_smoothing a ε q M ha hε hq2 hM
  refine ⟨η, hη, 0, ?_⟩
  intro N hNp _ inst ν f hf hν hnorm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  have hNorm : lpHat N q (fun x => (N : ℝ) * f x) ≤ M := by
    rw [scaled_norm]
    exact hnorm
  have hDom : ∀ x, 0 ≤ (N : ℝ) * f x ∧ (N : ℝ) * f x ≤ (N : ℝ) * ν x := by
    intro x
    exact ⟨mul_nonneg hNpos.le (hf x).1, mul_le_mul_of_nonneg_left (hf x).2 hNpos.le⟩
  have hMajor : ∀ r, ‖hatE N (fun x => (N : ℝ) * ν x) r - (if r = 0 then 1 else 0)‖ ≤ η := by
    intro r
    rw [scaled_transform]
    simpa using hν (-r)
  obtain ⟨G, hG, hmean, hclose, hGnorm⟩ := hSmooth N hNp
    (fun x => (N : ℝ) * f x) (fun x => (N : ℝ) * ν x) hDom hNorm hMajor
  refine ⟨fun x => G x / N, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨div_nonneg (hG x).1 hNpos.le, div_le_div_of_nonneg_right (hG x).2 hNpos.le⟩
  · have hFavg : avg N (fun x => (N : ℝ) * f x) = ∑ x, f x := by
      unfold avg
      rw [← mul_sum]
      field_simp
    have hGavg : (∑ x : ZMod N, G x / N) = avg N G := by
      rw [← sum_div, avg]
      ring
    rw [hGavg, hmean, hFavg]
  · intro r
    rw [probability_transform]
    have hh := hclose (-r)
    rw [scaled_transform] at hh
    simpa using hh
  · have hs : (∑ r : ZMod N, ‖fourierZN N (fun x => G x / N) r‖ ^ q) =
        ∑ r : ZMod N, ‖hatE N G r‖ ^ q := by
      simp_rw [probability_transform]
      exact Equiv.sum_comp (Equiv.neg _) (fun r => ‖hatE N G r‖ ^ q)
    rw [hs]
    exact hGnorm

end LeanLab.DensityGoldbach.Smoothing408

#print axioms LeanLab.DensityGoldbach.Smoothing408.normalized_smoothing

#print axioms LeanLab.DensityGoldbach.Smoothing408.scaled_transform
#print axioms LeanLab.DensityGoldbach.Smoothing408.probability_transform
#print axioms LeanLab.DensityGoldbach.Smoothing408.scaled_norm
#print axioms LeanLab.DensityGoldbach.Smoothing408.probability_smoothing

#print axioms LeanLab.DensityGoldbach.Smoothing408.residual_norm
