/-
Gallagher 1970 p.334 display 21 in the uniform height scale.
Source https://doi.org/10.1007/bf01403187
AI wrote this Lean code. Codex task335. Goldbach is open.
-/
import LeanLab.Linnik.Decomp1532b

open Finset Complex Set Metric
open scoped Classical
open LeanLab.PNTPort.DirichletZF LeanLab.Linnik.Decomp1532b LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp335c

/-- Gallagher pp.333 and 334 local multiplicity bound in the global height scale.
The additive one in the local count is absorbed by r log T at least one.
No lower bound on r log of B q t is imposed. -/
theorem local_disc_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
        |t| ≤ T → 0 < r → 1 ≤ r * Real.log T →
        (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
          (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤ C * r * Real.log T := by
  obtain ⟨C₀, hC₀, hsmall⟩ := local_disc_order_sum_nonprincipal_add_one
  obtain ⟨K, hK, hheight⟩ := log_Bt_le_log_height
  let C : ℝ := max (C₀ * (1 + K)) (8 * K / Real.log (10 / 9))
  have hlog : 0 < Real.log (10 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := (by positivity : 0 ≤ C₀ * (1 + K)).trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro T hT q hq hqT χ hχ t r ht hr hscale
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hB := hheight hT hqT ht
  by_cases hrl : r ≤ 1 / 8
  · have hcount := hsmall q χ hχ t r hr hrl
    have h1 : 1 + r * Real.log (Bt q t) ≤ (1 + K) * (r * Real.log T) := by
      have hh := mul_le_mul_of_nonneg_left hB hr.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC₀
    have h3 := mul_le_mul_of_nonneg_right (le_max_left (C₀ * (1 + K)) (8 * K / Real.log (10 / 9)))
      (mul_nonneg hr.le hL)
    exact hcount.trans (h2.trans (by dsimp [C]; nlinarith))
  · have htotal := zero_count_le hχ t
    have hsub : (∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
        (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤
        ∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    apply hsub.trans (htotal.trans ?_)
    have hCr : K / Real.log (10 / 9 : ℝ) ≤ C * r := by
      have hcle : 8 * K / Real.log (10 / 9 : ℝ) ≤ C := le_max_right _ _
      have hr8 : 1 / 8 ≤ r := le_of_not_ge hrl
      have hh := mul_le_mul_of_nonneg_left hr8 (by positivity : 0 ≤ 8 * K / Real.log (10 / 9 : ℝ))
      have hh' := mul_le_mul_of_nonneg_right hcle hr.le
      have he : (8 * K / Real.log (10 / 9 : ℝ)) * (1 / 8) = K / Real.log (10 / 9 : ℝ) := by ring
      rw [he] at hh
      exact hh.trans hh'
    calc
      Real.log (Bt q t) / Real.log (10 / 9) ≤ (K * Real.log T) / Real.log (10 / 9) :=
        div_le_div_of_nonneg_right hB hlog.le
      _ ≤ C * r * Real.log T := by
        have hh := mul_le_mul_of_nonneg_right hCr hL
        convert hh using 1 <;> ring

/-- Gallagher p.334 the far zero power tail in the global height scale. -/
theorem far_zero_pole_power_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r cutoff : ℝ),
      |t| ≤ T → 0 ≤ r → 0 < cutoff → 1 ≤ cutoff * Real.log T → ∀ k : ℕ, 1 ≤ k →
      ‖∑ ρ ∈ (zset hχ t).filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖),
        (analyticOrderNatAt (fShift χ t) ρ : ℂ) / ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
          C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, hlocal⟩ := local_disc_order_sum_global
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro T hT q hq hqT χ hχ t r cutoff ht hr hcutoff hscale k hk
  let S := (zset hχ t).filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖)
  let w : ℂ → ℝ := fun ρ => analyticOrderNatAt (fShift χ t) ρ
  let R : ℂ → ℝ := fun ρ => ‖ρ + (1 / 2 : ℂ)‖
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hmass (u : ℝ) (hu : cutoff ≤ u) : (∑ ρ ∈ S.filter (fun ρ => R ρ ≤ u), w ρ) ≤
      (C₀ * Real.log T) * u := by
    have hsub : S.filter (fun ρ => R ρ ≤ u) ⊆ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ u) := by
      intro ρ hρ
      obtain ⟨hρS, hρR⟩ := mem_filter.mp hρ
      exact mem_filter.mpr ⟨(mem_filter.mp hρS).1, hρR⟩
    have hsc : 1 ≤ u * Real.log T := hscale.trans (mul_le_mul_of_nonneg_right hu hlog)
    have h := (sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ hρ' => Nat.cast_nonneg _)).trans
      (hlocal T hT q hqT χ hχ t u ht (hcutoff.trans_le hu) hsc)
    convert h using 1 <;> ring
  have htail := finite_dyadic_reciprocal_tail S w R (mul_nonneg hC₀ hlog) hcutoff
    (fun ρ hρ => Nat.cast_nonneg _) (fun ρ hρ => (mem_filter.mp hρ).2.le) hmass hk
  calc
    _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt (fShift χ t) ρ : ℂ) /
        ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, w ρ / R ρ ^ (k + 1) := by
      apply sum_le_sum
      intro ρ hρ
      have hρz := (mem_zset.mp (mem_filter.mp hρ).1).2
      have hre : (ρ + (1 / 2 : ℂ)).re ≤ 0 := by
        have hreal : (ρ + ((3 : ℂ) / 2 + I * t)).re < 1 := by
          by_contra h
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρz
        norm_num at hreal ⊢
        linarith
      have hdist : R ρ ≤ ‖(r : ℂ) - 1 / 2 - ρ‖ := by
        have h := norm_shift_right_ge hre hr
        convert h using 1 <;> congr 1 <;> ring
      have hRpos : 0 < R ρ := hcutoff.trans (mem_filter.mp hρ).2
      rw [norm_div, norm_pow, Complex.norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hRpos _)
        (pow_le_pow_left₀ hRpos.le hdist _)
    _ ≤ _ := by convert htail using 1 <;> ring

/-- Gallagher p.334 display 21 in the global height scale for nonprincipal characters. -/
theorem near_zero_logDeriv_expansion_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r cutoff : ℝ),
      |t| ≤ T → 0 < r → r ≤ 1 / 8 → 0 < cutoff → cutoff ≤ 1 / 8 →
      1 ≤ cutoff * Real.log T → ∀ k : ℕ, 1 ≤ k →
      ‖iteratedDeriv k (logDeriv (fShift χ t)) ((r : ℂ) - 1 / 2) -
        (-1 : ℂ) ^ k * k.factorial *
          ∑ ρ ∈ (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff),
            (analyticOrderNatAt (fShift χ t) ρ : ℂ) / ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
        (k.factorial : ℝ) * C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, htail⟩ := far_zero_pole_power_sum_global
  obtain ⟨K, hK, hheight⟩ := log_Bt_le_log_height
  refine ⟨K0 * K + C₀, by have := K0_pos; positivity, ?_⟩
  intro T hT q hq hqT χ hχ t r cutoff ht hr hrl hc hcl hscale k hk
  let z : ℂ := (r : ℂ) - 1 / 2
  let a : ℂ := (-1 : ℂ) ^ k * k.factorial
  let f : ℂ → ℂ := fShift χ t
  let P : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1)
  let S := zset hχ t
  have hz : ‖z‖ ≤ 1 / 2 := by
    have he : z = ((r - 1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hne : f z ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    dsimp [z]
    norm_num
    linarith
  have hfull := iterated_logDeriv_pole_expansion_bound hχ t k hz hne
  have hlogBt : 0 ≤ Real.log (Bt q t) := Real.log_nonneg (one_lt_Bt t).le
  have hfull' := hfull.trans (show _ ≤ (k.factorial : ℝ) * K0 * (K * Real.log T) * 8 ^ k by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hheight hT hqT ht)
        (mul_nonneg (Nat.cast_nonneg k.factorial) K0_pos.le))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) k)
    convert hh using 1 <;> ring)
  have hfar := htail T hT q hqT χ hχ t r cutoff ht hr.le hc hscale k hk
  have hsplit : (∑ ρ ∈ S, P ρ) =
      (∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ) +
      (∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) := by
    simpa only [not_le] using (sum_filter_add_sum_filter_not S (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff) P).symm
  have ha : ‖a‖ = (k.factorial : ℝ) := by simp [a, norm_pow]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hp : (8 : ℝ) ^ k ≤ 1 / cutoff ^ k := by
    apply (le_div_iff₀ (pow_pos hc k)).2
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  have htriangle : ‖iteratedDeriv k (logDeriv f) z -
      a * ∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ‖ ≤
      ‖iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ‖ +
        (k.factorial : ℝ) * ‖∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ‖ := by
    rw [← ha, ← norm_mul]
    convert norm_add_le (iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ)
      (a * ∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) using 1
    congr 1
    rw [hsplit]
    ring
  apply htriangle.trans
  have hb := add_le_add hfull' (mul_le_mul_of_nonneg_left hfar (Nat.cast_nonneg k.factorial))
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg k.factorial) (mul_nonneg (mul_nonneg K0_pos.le hK.le) hlog))
  convert add_le_add_right hh ((k.factorial : ℝ) * (C₀ * Real.log T / cutoff ^ k)) using 1 <;> ring

/-- Gallagher p.334 the nonprincipal large derivative in the global height scale.
This includes local logarithmic scales below one. -/
theorem nonprincipal_large_logDeriv_global : ∃ E : ℝ, 1 ≤ E ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t r : ℝ),
      |t| ≤ T → 0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log T →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      ∀ M : ℕ, E * r * Real.log T ≤ M →
        ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
          (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) ≤
            ‖iteratedDeriv k (logDeriv (fShift χ t)) ((r : ℂ) - 1 / 2)‖ := by
  obtain ⟨C₀, hC₀, hcount⟩ := local_disc_order_sum_global
  obtain ⟨C₁, hC₁, hexp⟩ := near_zero_logDeriv_expansion_global
  let E : ℝ := max 1 (max (200 * C₀) (200 * C₁))
  have hE : 1 ≤ E := le_max_left _ _
  refine ⟨E, hE, ?_⟩
  intro T hT q hq hqT χ hχ t r ht hr hrl hscale hroot M hM
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hc : 0 < 200 * r := by positivity
  have hcl : 200 * r ≤ 1 / 8 := by linarith
  have hscale' : 1 ≤ (200 * r) * Real.log T := by nlinarith
  let S := (zset hχ t).filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ 200 * r)
  let m : ℂ → ℕ := fun ρ => analyticOrderNatAt (fShift χ t) ρ
  let s : ℂ := (r : ℂ) - 1 / 2
  have hMcount : (∑ ρ ∈ S, m ρ) ≤ M := by
    have hc₀ : 200 * C₀ ≤ E := (le_max_left _ _).trans (le_max_right _ _)
    have hbound := hcount T hT q hqT χ hχ t (200 * r) ht hc hscale'
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₀ hr.le) hlog
    have hcast : (∑ ρ ∈ S, (m ρ : ℝ)) ≤ M := hbound.trans (by nlinarith)
    exact_mod_cast hcast
  have hsne : fShift χ t s ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    dsimp [s]
    norm_num
    linarith
  have hne (ρ : ℂ) (hρ : ρ ∈ S) : s - ρ ≠ 0 := by
    intro he
    have hzero := (mem_zset.mp (mem_filter.mp hρ).1).2
    exact hsne (sub_eq_zero.mp he ▸ hzero)
  have hclose : ∃ ρ ∈ S, 0 < m ρ ∧ ‖s - ρ‖ ≤ 2 * r := by
    obtain ⟨ρ, hρ, hd⟩ := hroot
    let w := ρ - ((3 : ℂ) / 2 + I * t)
    have he : w + (1 / 2 : ℂ) = ρ - (1 + I * t) := by dsimp [w]; ring
    have hw : ‖w + (1 / 2 : ℂ)‖ ≤ r := by rwa [he]
    have hnorm : ‖w‖ ≤ 3 / 4 := by
      have hh := norm_sub_le (w + (1 / 2 : ℂ)) (1 / 2 : ℂ)
      norm_num at hh
      linarith
    have hzero : fShift χ t w = 0 := by simpa [fShift, w] using hρ
    have hwS : w ∈ S := mem_filter.mpr ⟨mem_zset.mpr ⟨hnorm, hzero⟩, by nlinarith⟩
    have hf : AnalyticOnNhd ℂ (fShift χ t) univ := fun z hz => fShift_analyticAt hχ t z
    have htop : analyticOrderAt (fShift χ t) w ≠ ⊤ :=
      hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ w)
        (by rw [analyticOrderAt_eq_zero.mpr (Or.inr (fShift_zero_ne χ t))]; simp)
    have hm : m w ≠ 0 := by
      simp only [m, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(fShift_analyticAt hχ t w).analyticOrderAt_ne_zero.mpr hzero, htop⟩
    refine ⟨w, hwS, Nat.pos_of_ne_zero hm, ?_⟩
    have hh := norm_sub_le (r : ℂ) (w + (1 / 2 : ℂ))
    have he' : s - w = (r : ℂ) - (w + (1 / 2 : ℂ)) := by dsimp [s]; ring
    rw [he']
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at hh
    linarith
  obtain ⟨ν, hν, hν', hpole⟩ := reciprocal_pole_turan S m id hMcount hr s hne hclose
  let k := ν - 1
  have hν0 : 0 < ν := by omega
  have hkν : k + 1 = ν := Nat.sub_add_cancel hν0
  have hkM : M ≤ k := by dsimp [k]; omega
  have hklt : k < 2 * M := by dsimp [k]; omega
  have hMpos : 1 ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hr.le) hlog
    have hmreal : (1 : ℝ) ≤ M := hscale.trans (by nlinarith)
    exact_mod_cast hmreal
  have hk : 1 ≤ k := hMpos.trans hkM
  have hCM : 200 * C₁ * r * Real.log T ≤ (k : ℝ) := by
    have hc₁ : 200 * C₁ ≤ E := (le_max_right _ _).trans (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ hr.le) hlog
    have hm : (M : ℝ) ≤ k := by exact_mod_cast hkM
    linarith
  have habs := reciprocal_pole_error_absorbed hr hCM
  have herr := hexp T hT q hqT χ hχ t r (200 * r) ht hr (by linarith) hc hcl hscale' k hk
  let F : ℂ := iteratedDeriv k (logDeriv (fShift χ t)) s
  let P : ℂ := (-1 : ℂ) ^ k * k.factorial * ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) ^ (k + 1)
  have hPn : (k.factorial : ℝ) / (100 * r) ^ (k + 1) ≤ ‖P‖ := by
    have hh := mul_le_mul_of_nonneg_left hpole (Nat.cast_nonneg k.factorial)
    simpa [P, norm_mul, norm_pow, hkν, mul_div_assoc, div_eq_mul_inv] using hh
  have hFn : ‖F - P‖ ≤ (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) := by
    exact herr.trans (by convert mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg k.factorial) using 1 <;> ring)
  have htriangle : ‖P‖ ≤ ‖F‖ + ‖F - P‖ := by
    have hh := norm_add_le F (P - F)
    rw [norm_sub_rev P F] at hh
    simpa only [add_sub_cancel] using hh
  refine ⟨k, hkM, hklt, ?_⟩
  have heq : (k.factorial : ℝ) / (100 * r) ^ (k + 1) =
      2 * ((k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1))) := by ring
  rw [heq] at hPn
  linarith

/-- Gallagher p.334 principal Euler factor auxiliary. The sum of the
logarithms of the distinct prime divisors is at most the modulus logarithm. -/
theorem sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    (∑ p ∈ q.primeFactors, Real.log p) ≤ Real.log q := by
  have hp (p : ℕ) (hp : p ∈ q.primeFactors) : 0 < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (prod_pos hp)
  rw [← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.prod_primeFactors_dvd q)

/-- Gallagher p.334 principal Euler factor auxiliary. Every Euler power
has norm at most three quarters in the half plane of real part at least one half. -/
theorem norm_prime_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc
    (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / Real.sqrt p := by rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, one_div]
    _ ≤ 3 / 4 := by
      have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
      have hs2 := Real.sq_sqrt hp0.le
      have hsnn := Real.sqrt_nonneg (p : ℝ)
      apply (div_le_iff₀ hs0).mpr
      nlinarith

/-- Gallagher p.334 principal Euler factor auxiliary. The finite Euler
logarithmic derivative correction has norm at most three log q on real part
at least one half. The identity with L prime over L is a separate step. -/
theorem norm_euler_log_correction_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖∑ p ∈ q.primeFactors,
      (Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))‖ ≤ 3 * Real.log q := by
  calc
    _ ≤ ∑ p ∈ q.primeFactors,
        ‖(Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, 3 * Real.log p := by
      apply sum_le_sum
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hz := norm_prime_cpow_neg_le hpp hs
      have hden : (1 / 4 : ℝ) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
        have hh := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
        norm_num only [norm_one] at hh
        linarith
      have hlog := Real.log_natCast_nonneg p
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
      calc
        Real.log p * ‖(p : ℂ) ^ (-s)‖ / ‖1 - (p : ℂ) ^ (-s)‖ ≤
            (Real.log p * (3 / 4)) / (1 / 4) := by
          apply div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left hz hlog) (by norm_num) hden
        _ = 3 * Real.log p := by ring
    _ = 3 * ∑ p ∈ q.primeFactors, Real.log p := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_log_primeFactors_le q) (by norm_num)

/-- Gallagher p.334 principal Euler correction is analytic on the
closed half plane of real part at least one half. -/
theorem analyticAt_euler_log_correction (q : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))) s := by
  apply Finset.analyticAt_fun_sum
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  have hpow : AnalyticAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hpn]
    fun_prop
  have hne : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    have hz := norm_prime_cpow_neg_le hpp hs
    intro he
    have hone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
    rw [hone, norm_one] at hz
    norm_num at hz
  exact (analyticAt_const.mul hpow).div (analyticAt_const.sub hpow) hne

/-- Gallagher p.334 differentiated principal Euler error auxiliary.
At every point of real part at least one, the kth derivative of the finite
Euler logarithmic correction is bounded by three k factorial log q times four to the k.
The identity with the principal logarithmic derivative remains separate. -/
theorem iteratedDeriv_euler_log_correction_le (q : ℕ) [NeZero q]
    (k : ℕ) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖iteratedDeriv k (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))) s‖ ≤
      (k.factorial : ℝ) * (3 * Real.log q) * 4 ^ k := by
  let f : ℂ → ℂ := fun z => ∑ p ∈ q.primeFactors,
    (Real.log p : ℂ) * (p : ℂ) ^ (-z) / (1 - (p : ℂ) ^ (-z))
  have hhalf {z : ℂ} (hz : ‖z - s‖ ≤ 1 / 4) : 1 / 2 ≤ z.re := by
    have hh := (Complex.abs_re_le_norm (z - s)).trans hz
    rw [Complex.sub_re, abs_le] at hh
    linarith [hh.1]
  have hdc : DiffContOnCl ℂ f (ball s (1 / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    intro z hz
    have hn : ‖z - s‖ ≤ 1 / 4 := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact (analyticAt_euler_log_correction q (hhalf hn)).differentiableAt.differentiableWithinAt
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by norm_num : (0 : ℝ) < 1 / 4) hdc (C := 3 * Real.log q) (by
      intro z hz
      have hn : ‖z - s‖ = 1 / 4 := by simpa [mem_sphere, dist_eq_norm] using hz
      exact norm_euler_log_correction_le q (hhalf hn.le))
  simpa only [one_div, inv_pow, div_inv_eq_mul] using hh

/-- Gallagher p.334 principal logarithmic derivative identity.
Away from the pole and the zeta zeros in the right half plane, the
principal logarithmic derivative is the zeta logarithmic derivative plus
the finite Euler correction bounded above. -/
theorem principal_logDeriv_eq_zeta_add_euler (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hsne : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    logDeriv (1 : DirichletCharacter ℂ q).LFunction s = logDeriv riemannZeta s +
      ∑ p ∈ q.primeFactors,
        (Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) := by
  let P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))
  have hfactor (p : ℕ) (hp : p ∈ q.primeFactors) : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    have hz := norm_prime_cpow_neg_le (Nat.prime_of_mem_primeFactors hp) hs
    intro he
    have hone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
    rw [hone, norm_one] at hz
    norm_num at hz
  have hderiv (p : ℕ) (hp : p ∈ q.primeFactors) :
      HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
        ((Real.log p : ℂ) * (p : ℂ) ^ (-s)) s := by
    have hp0 := (Nat.prime_of_mem_primeFactors hp).pos
    have hpn : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp0)
    have hh := ((hasDerivAt_id s).neg.const_cpow (.inl hpn)).const_sub 1
    have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log (by positivity : (0 : ℝ) ≤ p)]
    simpa only [Pi.neg_apply, id_eq, hlog, mul_neg, mul_one, neg_neg, neg_one_mul, one_mul, mul_comm] using hh
  have hP : P s ≠ 0 := prod_ne_zero_iff.mpr hfactor
  have hPd : DifferentiableAt ℂ P s :=
    DifferentiableAt.fun_finsetProd (fun p hp => (hderiv p hp).differentiableAt)
  have heq : (1 : DirichletCharacter ℂ q).LFunction =ᶠ[nhds s]
      (fun z => P z * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hsne] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz
  calc
    logDeriv (1 : DirichletCharacter ℂ q).LFunction s = logDeriv P s + logDeriv riemannZeta s := by
      rw [(logDeriv_congr_nhds heq).self_of_nhds,
        logDeriv_fun_mul s hP hzeta hPd (analyticAt_riemannZeta hsne).differentiableAt]
    _ = _ := by
      dsimp only [P]
      rw [logDeriv_fun_prod hfactor (fun p hp => (hderiv p hp).differentiableAt), add_comm]
      congr 1
      apply sum_congr rfl
      intro p hp
      rw [logDeriv_apply, (hderiv p hp).deriv]

/-- Gallagher pp.333 and 334 principal ambient multiplicity bound.
The finite zeta zero window has total multiplicity at most C log T.
The height exclusion is retained. -/
theorem zeta_window_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      ∀ hfin : (ZeroWindow t).Finite,
        (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log T := by
  obtain ⟨A, hA, hnorm⟩ := norm_logDeriv_right_halfplane
  obtain ⟨K, hK, herr⟩ := SumBoundI
  refine ⟨4 * (2 + A) + 2 * K, by positivity, ?_⟩
  intro T t hT ht htT hfin
  let s : ℂ := 1 + (1 / 2 : ℝ) + I * t
  let F : ℂ := deriv riemannZeta s / riemannZeta s
  let V : ℂ := ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)
  have hkey : ‖F - V‖ ≤ K * Real.log |t| := herr (1 / 2) (by constructor <;> norm_num) t ht hfin
  have hF : ‖F‖ ≤ 2 + A := by
    simpa [F, s, DirichletCharacter.LFunction_modOne_eq] using
      hnorm 1 1 t (1 / 2) (by constructor <;> norm_num)
  have hV : V.re ≤ 2 + A + K * Real.log |t| := by
    calc
      V.re ≤ ‖V‖ := Complex.re_le_norm _
      _ = ‖F - (F - V)‖ := by congr 1; ring
      _ ≤ ‖F‖ + ‖F - V‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hF hkey
  have hnear (ρ : ℂ) (hρ : ρ ∈ hfin.toFinset) :
      (analyticOrderNatAt riemannZeta ρ : ℝ) / 2 ≤
        ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re := by
    have hp := (Set.Finite.mem_toFinset hfin).mp hρ
    have hre : 1 / 2 ≤ (s - ρ).re := by
      have hrho : ρ.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hp.1)
      dsimp [s]
      norm_num
      linarith
    have hn : ‖s - ρ‖ ≤ 3 / 4 := by
      rw [norm_sub_rev]
      simpa only [s, show (1 : ℂ) + (1 / 2 : ℝ) = 3 / 2 by norm_num] using hp.2
    have hsq : Complex.normSq (s - ρ) ≤ (3 / 4 : ℝ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (s - ρ)]
    have hsqpos : 0 < Complex.normSq (s - ρ) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (s - ρ).im]
    simp only [Complex.div_re, Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    apply (le_div_iff₀ hsqpos).mpr
    have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
    have hlow := mul_le_mul_of_nonneg_left hre hm
    have hupp := mul_le_mul_of_nonneg_left hsq (div_nonneg hm (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith
  have hsum : (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) / 2 ≤ V.re := by
    dsimp only [V]
    rw [Complex.re_sum, sum_div]
    exact sum_le_sum hnear
  have hlog : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) htT
  have hhalf : (1 / 2 : ℝ) ≤ Real.log T := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    linarith [Real.log_two_gt_d9]
  have hmass := mul_le_mul_of_nonneg_left hlog hK.le
  have hconst := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * (2 + A) by linarith)
  nlinarith

/-- Gallagher pp.333 and 334 principal local density in the global height scale.
The bound is valid for every radius in the fixed ambient zeta window. -/
theorem zeta_disc_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T → 0 < r → 1 ≤ r * Real.log T →
      ∀ hfin : (ZeroWindow t).Finite,
        (∑ ρ ∈ hfin.toFinset.filter (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r),
          (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * r * Real.log T := by
  obtain ⟨C₀, hC₀, hsmall⟩ := local_disc_order_sum_zeta_add_one
  obtain ⟨C₁, hC₁, htotal⟩ := zeta_window_order_sum_global
  let C : ℝ := max (2 * C₀) (8 * C₁)
  refine ⟨C, (by positivity : 0 ≤ 2 * C₀).trans (le_max_left _ _), ?_⟩
  intro T t r hT ht htT hr hscale hfin
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  by_cases hrl : r ≤ 1 / 8
  · have hs := hsmall t r ht hr hrl hfin
    have hlogs := Real.log_le_log (by linarith : 0 < |t|) htT
    have h1 := mul_le_mul_of_nonneg_left hlogs hr.le
    have h2 := mul_le_mul_of_nonneg_left (show 1 + r * Real.log |t| ≤ 2 * (r * Real.log T) by nlinarith) hC₀
    have h3 := mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) (8 * C₁)) (mul_nonneg hr.le hL)
    dsimp only [C]
    nlinarith
  · have hsub := sum_le_sum_of_subset_of_nonneg
      (filter_subset (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r) hfin.toFinset)
      (fun ρ _ _ => (Nat.cast_nonneg (analyticOrderNatAt riemannZeta ρ) : (0 : ℝ) ≤ _))
    have hs := htotal T t hT ht htT hfin
    have hcoeff : C₁ ≤ C * r := by
      have hh := mul_le_mul_of_nonneg_left (show 1 / 8 ≤ r by linarith) (show 0 ≤ 8 * C₁ by positivity)
      have hh' := mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) (8 * C₁)) hr.le
      dsimp only [C]
      nlinarith
    exact hsub.trans (hs.trans (by convert mul_le_mul_of_nonneg_right hcoeff hL using 1 <;> ring))

/-- Gallagher p.334 the global principal local count in shifted coordinates.
The statement applies to any finite set of zeros in the fixed ambient disc. -/
theorem zeta_shift_local_order_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T → 0 < r → 1 ≤ r * Real.log T →
      ∀ S : Finset ℂ,
        (∀ ρ ∈ S, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4) →
        (∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r),
          (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℝ)) ≤
            C * r * Real.log T := by
  obtain ⟨C, hC, hcount⟩ := zeta_disc_order_sum_global
  refine ⟨C, hC, ?_⟩
  intro T t r hT ht htT hr hscale S hS
  let c : ℂ := 3 / 2 + I * t
  let V := S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ r)
  let U := V.image (fun ρ => ρ + c)
  let hfin := ZeroWindowFinite ht
  have hsub : U ⊆ hfin.toFinset.filter (fun ρ => ‖ρ - (1 + I * t)‖ ≤ r) := by
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp hz
    obtain ⟨hρS, hρnear⟩ := mem_filter.mp hρ
    apply mem_filter.mpr
    constructor
    · apply (Set.Finite.mem_toFinset hfin).mpr
      constructor
      · simpa [c, add_assoc] using (hS ρ hρS).1
      · simpa [c] using (hS ρ hρS).2
    · have he : ρ + c - (1 + I * t) = ρ + 1 / 2 := by dsimp [c]; ring
      rwa [he]
  have hord (ρ : ℂ) :
      analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ =
        analyticOrderNatAt riemannZeta (ρ + c) := by
    have hf : (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) =
        (fun w : ℂ => riemannZeta (w + c)) := by
      funext w
      dsimp [c]
      congr 1
      ring
    rw [hf, analyticOrderNatAt_fun_comp_add_right]
  have heq : (∑ ρ ∈ V,
      (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℝ)) =
        ∑ z ∈ U, (analyticOrderNatAt riemannZeta z : ℝ) := by
    dsimp only [U]
    rw [sum_image (fun a ha b hb h => by exact add_right_cancel h)]
    simp only [hord]
  change (∑ ρ ∈ V, _) ≤ _
  rw [heq]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
    (hcount T t r hT ht htT hr hscale hfin)

/-- Gallagher p.334 the principal far zero power tail in the global height scale. -/
theorem zeta_far_zero_pole_power_sum_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r cutoff : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      0 ≤ r → 0 < cutoff → 1 ≤ cutoff * Real.log T → ∀ k : ℕ, 1 ≤ k →
      ∀ S₀ : Finset ℂ,
        (∀ ρ ∈ S₀, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4) →
        ‖∑ ρ ∈ S₀.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖),
          (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℂ) /
            ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤ C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, hlocal⟩ := zeta_shift_local_order_sum_global
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro T t r cutoff hT ht htT hr hcutoff hscale k hk S₀ hS
  let f : ℂ → ℂ := fun w => riemannZeta (w + 3 / 2 + I * t)
  let S := S₀.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖)
  let w : ℂ → ℝ := fun ρ => analyticOrderNatAt f ρ
  let R : ℂ → ℝ := fun ρ => ‖ρ + (1 / 2 : ℂ)‖
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hmass (u : ℝ) (hu : cutoff ≤ u) : (∑ ρ ∈ S.filter (fun ρ => R ρ ≤ u), w ρ) ≤
      (C₀ * Real.log T) * u := by
    have hsub : S.filter (fun ρ => R ρ ≤ u) ⊆ S₀.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ u) := by
      intro ρ hρ
      obtain ⟨hρS, hρR⟩ := mem_filter.mp hρ
      exact mem_filter.mpr ⟨(mem_filter.mp hρS).1, hρR⟩
    have hsc : 1 ≤ u * Real.log T := hscale.trans (mul_le_mul_of_nonneg_right hu hlog)
    have hh := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
      (hlocal T t u hT ht htT (hcutoff.trans_le hu) hsc S₀ hS)
    convert hh using 1 <;> ring
  have htail := finite_dyadic_reciprocal_tail S w R (mul_nonneg hC₀ hlog) hcutoff
    (fun _ _ => Nat.cast_nonneg _) (fun _ hρ => (mem_filter.mp hρ).2.le) hmass hk
  calc
    _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt f ρ : ℂ) /
        ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, w ρ / R ρ ^ (k + 1) := by
      apply sum_le_sum
      intro ρ hρ
      have hρz := (hS ρ (mem_filter.mp hρ).1).1
      have hre : (ρ + (1 / 2 : ℂ)).re ≤ 0 := by
        have hreal : (ρ + 3 / 2 + I * t).re < 1 :=
          lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hρz)
        norm_num at hreal ⊢
        linarith
      have hdist : R ρ ≤ ‖(r : ℂ) - 1 / 2 - ρ‖ := by
        have hh := norm_shift_right_ge hre hr
        convert hh using 1 <;> congr 1 <;> ring
      have hRpos : 0 < R ρ := hcutoff.trans (mem_filter.mp hρ).2
      rw [norm_div, norm_pow, Complex.norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hRpos _)
        (pow_le_pow_left₀ hRpos.le hdist _)
    _ ≤ _ := by convert htail using 1 <;> ring

/-- Gallagher p.334 display 21 in the global height scale for zeta.
The principal height exclusion is retained. -/
theorem zeta_near_zero_logDeriv_expansion_global : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T t r cutoff : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      0 < r → r ≤ 1 / 8 → 0 < cutoff → cutoff ≤ 1 / 8 →
      1 ≤ cutoff * Real.log T →
      ∀ hfin : (SetOfZeros 1 (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t))).Finite,
      ∀ k : ℕ, 1 ≤ k →
      ‖iteratedDeriv k (logDeriv (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t))) ((r : ℂ) - 1 / 2) -
        (-1 : ℂ) ^ k * k.factorial *
          ∑ ρ ∈ ((finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset).filter
              (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff),
            (analyticOrderNatAt (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)) ρ : ℂ) /
              ((r : ℂ) - 1 / 2 - ρ) ^ (k + 1)‖ ≤
        (k.factorial : ℝ) * C * Real.log T / cutoff ^ k := by
  obtain ⟨C₀, hC₀, htail⟩ := zeta_far_zero_pole_power_sum_global
  obtain ⟨A, hA, hfullbound⟩ := iterated_zeta_logDeriv_pole_expansion_bound
  refine ⟨A + C₀, by positivity, ?_⟩
  intro T t r cutoff hT ht htT hr hrl hc hcl hscale hfin k hk
  let z : ℂ := (r : ℂ) - 1 / 2
  let a : ℂ := (-1 : ℂ) ^ k * k.factorial
  let f : ℂ → ℂ := fun w => riemannZeta (w + 3 / 2 + I * t)
  let P : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) / (z - ρ) ^ (k + 1)
  let S := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset
  have hS : ∀ ρ ∈ S, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4 := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset _).mp hρ
    exact ⟨hh.2, hh.1⟩
  have hz : ‖z‖ ≤ 1 / 2 := by
    have he : z = ((r - 1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hne : f z ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp [z]
    norm_num
    linarith
  have hfull := hfullbound t ht hfin k z hz hne
  have hfull' := hfull.trans (show _ ≤ (k.factorial : ℝ) * A * Real.log T * 8 ^ k by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith : 0 < |t|) htT)
        (mul_nonneg (Nat.cast_nonneg k.factorial) hA.le))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) k)
    convert hh using 1 <;> ring)
  have hfar := htail T t r cutoff hT ht htT hr.le hc hscale k hk S hS
  have hsplit : (∑ ρ ∈ S, P ρ) =
      (∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ) +
      (∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) := by
    simpa only [not_le] using (sum_filter_add_sum_filter_not S (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff) P).symm
  have ha : ‖a‖ = (k.factorial : ℝ) := by simp [a, norm_pow]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hp : (8 : ℝ) ^ k ≤ 1 / cutoff ^ k := by
    apply (le_div_iff₀ (pow_pos hc k)).2
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  have htriangle : ‖iteratedDeriv k (logDeriv f) z -
      a * ∑ ρ ∈ S.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ cutoff), P ρ‖ ≤
      ‖iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ‖ +
        (k.factorial : ℝ) * ‖∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ‖ := by
    rw [← ha, ← norm_mul]
    convert norm_add_le (iteratedDeriv k (logDeriv f) z - a * ∑ ρ ∈ S, P ρ)
      (a * ∑ ρ ∈ S.filter (fun ρ => cutoff < ‖ρ + (1 / 2 : ℂ)‖), P ρ) using 1
    congr 1
    rw [hsplit]
    ring
  apply htriangle.trans
  have hb := add_le_add hfull' (mul_le_mul_of_nonneg_left hfar (Nat.cast_nonneg k.factorial))
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg k.factorial) (mul_nonneg hA.le hlog))
  convert add_le_add_right hh ((k.factorial : ℝ) * (C₀ * Real.log T / cutoff ^ k)) using 1 <;> ring


/-- Gallagher p.334 the principal zeta large derivative in the global height scale.
The height exclusion is retained and there are no character Euler factors in this step. -/
theorem zeta_large_logDeriv_global : ∃ E : ℝ, 1 ≤ E ∧
    ∀ T t r : ℝ, 2 ≤ T → 2 ≤ |t| → |t| ≤ T →
      0 < r → r ≤ 1 / 1600 → 1 ≤ r * Real.log T →
      (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      ∀ M : ℕ, E * r * Real.log T ≤ M →
        ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
          (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) ≤
            ‖iteratedDeriv k (logDeriv (fun w : ℂ => riemannZeta (w + 3 / 2 + I * t)))
              ((r : ℂ) - 1 / 2)‖ := by
  obtain ⟨C₀, hC₀, hcount⟩ := zeta_shift_local_order_sum_global
  obtain ⟨C₁, hC₁, hexp⟩ := zeta_near_zero_logDeriv_expansion_global
  let E : ℝ := max 1 (max (200 * C₀) (200 * C₁))
  have hE : 1 ≤ E := le_max_left _ _
  refine ⟨E, hE, ?_⟩
  intro T t r hT ht htT hr hrl hscale hroot M hM
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hc : 0 < 200 * r := by positivity
  have hcl : 200 * r ≤ 1 / 8 := by linarith
  have hscale' : 1 ≤ (200 * r) * Real.log T := by nlinarith
  let f : ℂ → ℂ := fun w => riemannZeta (w + 3 / 2 + I * t)
  let hfin := ZetaShiftFiniteZeros ht (f := f) rfl
  let S₀ := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset
  have hS₀ : ∀ ρ ∈ S₀, riemannZeta (ρ + 3 / 2 + I * t) = 0 ∧ ‖ρ‖ ≤ 3 / 4 := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset _).mp hρ
    exact ⟨hh.2, hh.1⟩
  let S := S₀.filter (fun ρ => ‖ρ + (1 / 2 : ℂ)‖ ≤ 200 * r)
  let m : ℂ → ℕ := fun ρ => analyticOrderNatAt f ρ
  let s : ℂ := (r : ℂ) - 1 / 2
  have hMcount : (∑ ρ ∈ S, m ρ) ≤ M := by
    have hc₀ : 200 * C₀ ≤ E := (le_max_left _ _).trans (le_max_right _ _)
    have hbound := hcount T t (200 * r) hT ht htT hc hscale' S₀ hS₀
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₀ hr.le) hlog
    have hcast : (∑ ρ ∈ S, (m ρ : ℝ)) ≤ M := hbound.trans (by nlinarith)
    exact_mod_cast hcast
  have hsne : f s ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp [s]
    norm_num
    linarith
  have hne (ρ : ℂ) (hρ : ρ ∈ S) : s - ρ ≠ 0 := by
    intro he
    have hzero := (hS₀ ρ (mem_filter.mp hρ).1).1
    exact hsne (sub_eq_zero.mp he ▸ hzero)
  have hclose : ∃ ρ ∈ S, 0 < m ρ ∧ ‖s - ρ‖ ≤ 2 * r := by
    obtain ⟨ρ, hρ, hd⟩ := hroot
    let w := ρ - ((3 : ℂ) / 2 + I * t)
    have he : w + (1 / 2 : ℂ) = ρ - (1 + I * t) := by dsimp [w]; ring
    have hw : ‖w + (1 / 2 : ℂ)‖ ≤ r := by rwa [he]
    have hnorm : ‖w‖ ≤ 3 / 4 := by
      have hh := norm_sub_le (w + (1 / 2 : ℂ)) (1 / 2 : ℂ)
      norm_num at hh
      linarith
    have hew : w + 3 / 2 + I * t = ρ := by dsimp [w]; ring
    have hzero : f w = 0 := by simpa only [f, hew] using hρ
    have hwS : w ∈ S := mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨hnorm, hzero⟩, by nlinarith⟩
    have hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) := by
      intro u hu
      have hnormu : ‖u‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hu
      have hsne' : u + 3 / 2 + I * (t : ℂ) ≠ 1 := by
        intro he'
        have hi := congrArg Complex.im he'
        simp only [add_im, div_ofNat_im, im_ofNat, zero_div, mul_im, I_re, ofReal_im,
          mul_zero, I_im, ofReal_re, one_mul, zero_add, one_im] at hi
        have habs := Complex.abs_im_le_norm u
        have hh : u.im = -t := by linarith
        rw [hh, abs_neg] at habs
        linarith
      exact AnalyticAt.fun_comp (analyticAt_riemannZeta hsne')
        ((analyticAt_id.fun_add analyticAt_const).fun_add analyticAt_const)
    have h0 : f 0 ≠ 0 := by
      dsimp [f]
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    have hwball : w ∈ closedBall (0 : ℂ) 1 := by
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have htop : analyticOrderAt f w ≠ ⊤ :=
      hf.analyticOrderAt_ne_top_of_isPreconnected Metric.isPreconnected_closedBall
        (show (0 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp) hwball
        (by rw [analyticOrderAt_eq_zero.mpr (Or.inr h0)]; simp)
    have hm : m w ≠ 0 := by
      simp only [m, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(hf w hwball).analyticOrderAt_ne_zero.mpr hzero, htop⟩
    refine ⟨w, hwS, Nat.pos_of_ne_zero hm, ?_⟩
    have hh := norm_sub_le (r : ℂ) (w + (1 / 2 : ℂ))
    have he' : s - w = (r : ℂ) - (w + (1 / 2 : ℂ)) := by dsimp [s]; ring
    rw [he']
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at hh
    linarith
  obtain ⟨ν, hν, hν', hpole⟩ := reciprocal_pole_turan S m id hMcount hr s hne hclose
  let k := ν - 1
  have hν0 : 0 < ν := by omega
  have hkν : k + 1 = ν := Nat.sub_add_cancel hν0
  have hkM : M ≤ k := by dsimp [k]; omega
  have hklt : k < 2 * M := by dsimp [k]; omega
  have hMpos : 1 ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hr.le) hlog
    have hmreal : (1 : ℝ) ≤ M := hscale.trans (by nlinarith)
    exact_mod_cast hmreal
  have hk : 1 ≤ k := hMpos.trans hkM
  have hCM : 200 * C₁ * r * Real.log T ≤ (k : ℝ) := by
    have hc₁ : 200 * C₁ ≤ E := (le_max_right _ _).trans (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ hr.le) hlog
    have hm : (M : ℝ) ≤ k := by exact_mod_cast hkM
    linarith
  have habs := reciprocal_pole_error_absorbed hr hCM
  have herr := hexp T t r (200 * r) hT ht htT hr (by linarith) hc hcl hscale' hfin k hk
  let F : ℂ := iteratedDeriv k (logDeriv (f)) s
  let P : ℂ := (-1 : ℂ) ^ k * k.factorial * ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) ^ (k + 1)
  have hPn : (k.factorial : ℝ) / (100 * r) ^ (k + 1) ≤ ‖P‖ := by
    have hh := mul_le_mul_of_nonneg_left hpole (Nat.cast_nonneg k.factorial)
    simpa [P, norm_mul, norm_pow, hkν, mul_div_assoc, div_eq_mul_inv] using hh
  have hFn : ‖F - P‖ ≤ (k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1)) := by
    exact herr.trans (by convert mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg k.factorial) using 1 <;> ring)
  have htriangle : ‖P‖ ≤ ‖F‖ + ‖F - P‖ := by
    have hh := norm_add_le F (P - F)
    rw [norm_sub_rev P F] at hh
    simpa only [add_sub_cancel] using hh
  refine ⟨k, hkM, hklt, ?_⟩
  have heq : (k.factorial : ℝ) / (100 * r) ^ (k + 1) =
      2 * ((k.factorial : ℝ) / (2 * (100 * r) ^ (k + 1))) := by ring
  rw [heq] at hPn
  linarith


end LeanLab.Linnik.Decomp335c
