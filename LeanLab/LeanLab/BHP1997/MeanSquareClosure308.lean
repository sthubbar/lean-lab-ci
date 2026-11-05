/-
BHP1997, page 3 condition iv and page 53 finite assembly.
The character estimates remain explicit inputs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.ShortConditions308
import LeanLab.BHP1997.WindowIntegrability308

namespace LeanLab.BHP1997.Task308
open Classical Complex MeasureTheory DecompC165b

/-- Page 3 condition iv. Two finite moving-window sums have squared integral
at most twice the sum of their squared integrals. All integrals are genuine. -/
theorem window_sum_sq_add_bound {ι : Type*} (E : Finset ι) (S : Finset ℕ)
    (c d : ι → ℕ → ℂ) (z : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∑ χ ∈ E, ∫ y in a..b, ‖∑ m ∈ S.filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), (c χ m + d χ m)‖ ^ 2) ≤
      2 * ((∑ χ ∈ E, ∫ y in a..b, ‖∑ m ∈ S.filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c χ m‖ ^ 2) +
        ∑ χ ∈ E, ∫ y in a..b, ‖∑ m ∈ S.filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), d χ m‖ ^ 2) := by
  have hχ (χ : ι) (hχ : χ ∈ E) :
      (∫ y in a..b, ‖∑ m ∈ S.filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), (c χ m + d χ m)‖ ^ 2) ≤
      2 * ((∫ y in a..b, ‖∑ m ∈ S.filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c χ m‖ ^ 2) +
        ∫ y in a..b, ‖∑ m ∈ S.filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), d χ m‖ ^ 2) := by
    have hc := window_sum_sq_intervalIntegrable S (c χ) z a b
    have hd := window_sum_sq_intervalIntegrable S (d χ) z a b
    have hsum := window_sum_sq_intervalIntegrable S (fun m => c χ m + d χ m) z a b
    have hh := intervalIntegral.integral_mono hab hsum ((hc.add hd).const_mul 2) (fun y => ?_)
    · simpa only [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hc hd] using hh
    · rw [Finset.sum_add_distrib]
      have ht := norm_add_le
        (∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c χ m)
        (∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), d χ m)
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg (‖∑ m ∈ S.filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c χ m‖ -
        ‖∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), d χ m‖)]
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib] using Finset.sum_le_sum hχ

/-- Page 3 condition iv and page 53 finite assembly. Adding two coefficient
families adds their densities. The exceptional character sets are united.
CONDITIONAL on both actual mean square estimates. -/
theorem short_mean_square_add {ε u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : ShortMeanSquare ε u a) (hb : ShortMeanSquare ε v b) :
    ShortMeanSquare ε (u+v) (fun x k => a x k+b x k) := by
  obtain ⟨Ea, ha⟩ := ha
  obtain ⟨Eb, hb⟩ := hb
  refine ⟨fun A x q => Ea A x q ∪ Eb A x q, ?_⟩
  intro A hA
  obtain ⟨Ca, hCa⟩ := ha A hA
  obtain ⟨Cb, hCb⟩ := hb A hA
  let C := max (max Ca Cb) (max 1 (max (Ca+Cb) (2*(Ca+Cb))))
  refine ⟨C, fun x hx q hq hqQ => ?_⟩
  have hxCa : Ca ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxCb : Cb ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx1 : 1 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hCC : Ca+Cb ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC2 : 2*(Ca+Cb) ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨hcarda, hinta⟩ := hCa x hxCa q hq hqQ
  obtain ⟨hcardb, hintb⟩ := hCb x hxCb q hq hqQ
  constructor
  · have hcard : ((Ea A x q ∪ Eb A x q).card : ℝ) ≤
        (Ea A x q).card + (Eb A x q).card := by
      exact_mod_cast Finset.card_union_le (Ea A x q) (Eb A x q)
    calc
      _ ≤ ((Ea A x q).card : ℝ) + ((Eb A x q).card : ℝ) := hcard
      _ ≤ Ca * (q : ℝ) ^ (1/2 : ℝ) * Real.log x ^ (-2*A) +
          Cb * (q : ℝ) ^ (1/2 : ℝ) * Real.log x ^ (-2*A) := add_le_add hcarda hcardb
      _ = (Ca+Cb) * (q : ℝ) ^ (1/2 : ℝ) * Real.log x ^ (-2*A) := by ring
      _ ≤ C * (q : ℝ) ^ (1/2 : ℝ) * Real.log x ^ (-2*A) := by
        gcongr
  · intro z hzl hzu
    have hY : 0 < x ^ (11/20+ε) := Real.rpow_pos_of_pos (by linarith) _
    have hab : x ^ (11/20+ε) / 2 ≤ 3 * x ^ (11/20+ε) := by linarith
    let E := (Finset.univ : Finset (DirichletCharacter ℂ q)) \ (Ea A x q ∪ Eb A x q)
    let ca : DirichletCharacter ℂ q → ℕ → ℂ := fun χ m =>
      (a x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * u / Real.log (x ^ (11/20+ε))
    let cb : DirichletCharacter ℂ q → ℕ → ℂ := fun χ m =>
      (b x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * v / Real.log (x ^ (11/20+ε))
    have hbound := window_sum_sq_add_bound E (rightInterval ε x) ca cb z hab
    have he (χ : DirichletCharacter ℂ q) (m : ℕ) :
        (((a x m + b x m : ℝ) : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * ((u+v : ℝ) : ℂ) / Real.log (x ^ (11/20+ε))) = ca χ m + cb χ m := by
      dsimp [ca, cb]
      push_cast
      ring
    dsimp only
    simp_rw [he]
    have hnonneg (f : DirichletCharacter ℂ q → ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
        0 ≤ ∫ y in (x ^ (11/20+ε)/2)..(3*x ^ (11/20+ε)),
          ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y+y*z), f χ m‖ ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun y hy => sq_nonneg _)
    have hEa : E ⊆ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ Ea A x q := by
      intro χ hχ
      simp only [E, Finset.mem_sdiff, Finset.mem_union, not_or] at hχ ⊢
      exact ⟨hχ.1, hχ.2.1⟩
    have hEb : E ⊆ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ Eb A x q := by
      intro χ hχ
      simp only [E, Finset.mem_sdiff, Finset.mem_union, not_or] at hχ ⊢
      exact ⟨hχ.1, hχ.2.2⟩
    have hsa := Finset.sum_le_sum_of_subset_of_nonneg hEa (fun χ hχ hnot => hnonneg ca χ)
    have hsb := Finset.sum_le_sum_of_subset_of_nonneg hEb (fun χ hχ hnot => hnonneg cb χ)
    have hba := (show _ ≤ _ from hsa).trans (hinta z hzl hzu)
    have hbb := (show _ ≤ _ from hsb).trans (hintb z hzl hzu)
    have hsum := hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hba hbb) (by norm_num : (0 : ℝ) ≤ 2))
    calc
      _ ≤ 2 * (Ca * ((q : ℝ) * sieveQ ε x)^2 * x ^ (11/20+ε) * Real.log x ^ (-A) +
          Cb * ((q : ℝ) * sieveQ ε x)^2 * x ^ (11/20+ε) * Real.log x ^ (-A)) := hsum
      _ = 2*(Ca+Cb) * ((q : ℝ) * sieveQ ε x)^2 * x ^ (11/20+ε) * Real.log x ^ (-A) := by ring
      _ ≤ C * ((q : ℝ) * sieveQ ε x)^2 * x ^ (11/20+ε) * Real.log x ^ (-A) := by
        gcongr

/-- Page 3 condition iv. Negating a coefficient family negates its density
and preserves the same mean square estimate and exceptional sets.
CONDITIONAL on the actual input estimate. -/
theorem short_mean_square_neg {ε u : ℝ} {a : ℝ → ℕ → ℝ}
    (ha : ShortMeanSquare ε u a) :
    ShortMeanSquare ε (-u) (fun x k => -a x k) := by
  obtain ⟨E, ha⟩ := ha
  refine ⟨E, fun A hA => ?_⟩
  obtain ⟨C, hC⟩ := ha A hA
  refine ⟨C, fun x hx q hq hqQ => ?_⟩
  obtain ⟨hcard, hint⟩ := hC x hx q hq hqQ
  refine ⟨hcard, fun z hzl hzu => ?_⟩
  have he (χ : DirichletCharacter ℂ q) (y : ℝ) :
      (∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y+y*z),
        (((-a x m : ℝ) : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * ((-u : ℝ) : ℂ) / Real.log (x ^ (11/20+ε)))) =
      -(∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y+y*z),
        ((a x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * u / Real.log (x ^ (11/20+ε)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    push_cast
    ring
  simp_rw [he, norm_neg]
  exact hint z hzl hzu

/-- Page 3 condition iv and page 53 finite assembly. Subtracting two coefficient
families subtracts their densities. CONDITIONAL on both actual input estimates. -/
theorem short_mean_square_sub {ε u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : ShortMeanSquare ε u a) (hb : ShortMeanSquare ε v b) :
    ShortMeanSquare ε (u-v) (fun x k => a x k-b x k) := by
  simpa only [sub_eq_add_neg] using short_mean_square_add ha (short_mean_square_neg hb)

end LeanLab.BHP1997.Task308
