/-
P0069 page 51 display 5.17. The prime number theorem input is separate from rough number density.
The lab already proves the required prime counting estimate in PNTPort.BVMax.PrimesUncond.
This file takes the difference of two prefix estimates.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.BVMax.PrimesUncond
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.SieveConditionsC165

namespace LeanLab.BHP1997.Prime514
open Classical
open scoped BigOperators
open LeanLab.PNTPort.BVMax
open LeanLab.BHP1997.Decomp132
open LeanLab.BHP1997.DecompC165b

/-- P0069 page 51 display 5.17. The prime count minus the discrete logarithmic integral\non a finite integer interval is the difference of the two prefix errors. -/
theorem prime_interval_error_eq {L U : ℕ} (hLU : L ≤ U) :
    ∑ m ∈ Finset.Ioc L U, (primeWeight m - 1 / Real.log (m : ℝ)) =
      (piN U 1 1 - liN U) - (piN L 1 1 - liN L) := by
  have hprefix (N : ℕ) :
      (∑ m ∈ Finset.Icc 1 N, (primeWeight m - 1 / Real.log (m : ℝ))) =
        piN N 1 1 - liN N := by
    rw [Finset.sum_sub_distrib]
    unfold primeWeight piN liN
    congr 1
    simp only [Nat.mod_one, true_and]
    simp
  have hsplit := Finset.sum_Ioc_consecutive
    (fun m => primeWeight m - 1 / Real.log (m : ℝ)) (Nat.zero_le L) hLU
  have hinterval (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simp only [hinterval, hprefix] at hsplit
  linarith

/-- P0069 page 51 display 5.17, its prime number theorem input.\nFor any positive log exponent, the prime count on every subinterval of the ambient interval\nis approximated by the discrete logarithmic integral with a uniform log power error.\nThe displayed cutoff condition is the q equal to one condition of the existing lab PNT. -/
theorem pnt_short_interval_with_cutoff (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X →
      1 ≤ Real.sqrt X / Real.log X ^ B → ∀ a b : ℝ,
        0 ≤ a → a ≤ b → b ≤ X →
        |∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (primeWeight m - 1 / Real.log (m : ℝ))| ≤
          2 * K * X / Real.log X ^ A := by
  obtain ⟨B, hB, K, hK⟩ := pi_sub_liD A hA
  refine ⟨B, hB, K, fun X hX hQ a b ha hab hb => ?_⟩
  have h1 := hK X hX hQ a ha (hab.trans hb)
  have h2 := hK X hX hQ b (ha.trans hab) hb
  rw [prime_interval_error_eq (Nat.floor_le_floor hab)]
  change |(LeanLab.PNTPort.BVMax.piAP b 1 1 - liD b) - (LeanLab.PNTPort.BVMax.piAP a 1 1 - liD a)| ≤ _
  calc _ ≤ |LeanLab.PNTPort.BVMax.piAP b 1 1 - liD b| + |LeanLab.PNTPort.BVMax.piAP a 1 1 - liD a| := abs_sub _ _
    _ ≤ K * X / Real.log X ^ A + K * X / Real.log X ^ A := add_le_add h2 h1
    _ = _ := by ring

/-- P0069 page 51 display 5.17. The auxiliary q equal to one cutoff\nholds for every sufficiently large ambient scale. This also supplies nonempty instances\nof the cutoff hypothesis in the preceding theorem. -/
theorem pnt_cutoff_eventually (B : ℝ) :
    ∃ C : ℝ, ∀ X : ℝ, C ≤ X → 2 ≤ X ∧ 1 ≤ Real.sqrt X / Real.log X ^ B := by
  have h := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp
    (h.and (Filter.eventually_ge_atTop (2 : ℝ)))
  refine ⟨C, fun X hX => ?_⟩
  obtain ⟨hb, hX2⟩ := hC X hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hpow : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hlog _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpow,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < X) _),
    ← Real.sqrt_eq_rpow] at hb
  refine ⟨hX2, (le_div_iff₀ hpow).mpr ?_⟩
  have := Real.sqrt_nonneg X
  nlinarith

/-- P0069 page 51 display 5.17, the prime input with its scale threshold chosen once.\nThis is the prime number theorem for arbitrary subintervals with an absolute log power error.\nIt makes no claim about the rough number density terms. -/
theorem pnt_short_interval (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ X : ℝ, C ≤ X → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ X →
      |∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (primeWeight m - 1 / Real.log (m : ℝ))| ≤
        C * X * Real.log X ^ (-A) := by
  obtain ⟨B, hB, K, hK⟩ := pnt_short_interval_with_cutoff A hA
  obtain ⟨C0, hC0⟩ := pnt_cutoff_eventually B
  let C := max (max C0 (2 * K)) 2
  have h0 : C0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hKc : 2 * K ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C, fun X hX a b ha hab hb => ?_⟩
  obtain ⟨hX2, hQ⟩ := hC0 X (h0.trans hX)
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hscale : 0 ≤ X / Real.log X ^ A := by positivity
  have hbound := hK X hX2 hQ a b ha hab hb
  calc _ ≤ 2 * K * X / Real.log X ^ A := hbound
    _ ≤ C * X / Real.log X ^ A := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hKc hscale
    _ = _ := by rw [Real.rpow_neg hlog.le, div_eq_mul_inv]

/-- P0069 page 3 display 1.8 and page 51 display 5.17.
Partition a prime character sum into its residue classes. -/
theorem prime_character_prefix_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (primeWeight n : ℂ) * χ (n : ZMod q) =
      ∑ a : ZMod q, χ a * (piN N q a.val : ℝ) := by
  have hpi (a : ZMod q) : (piN N q a.val : ℂ) =
      ∑ n ∈ Finset.Icc 1 N, if (n : ZMod q) = a then (primeWeight n : ℂ) else 0 := by
    have he (n : ℕ) :
        (if (n : ZMod q) = a then (primeWeight n : ℂ) else 0) =
          if n % q = a.val % q ∧ n.Prime then (1 : ℂ) else 0 := by
      have hn : (n : ZMod q) = a ↔ n % q = a.val % q := by
        simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff' n a.val q)
      by_cases hp : n.Prime <;> by_cases hna : (n : ZMod q) = a <;>
        simp [primeWeight, hp, hna, ← hn]
    simp_rw [he]
    simp [piN]
  simp_rw [hpi, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [eq_comm, mul_comm]

/-- P0069 page 3 display 1.8. For a nonprincipal character, the uniform
residue class main term cancels. A common prime counting error E costs at most q E. -/
theorem prime_character_error_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) (M E : ℝ) (hE : 0 ≤ E)
    (hpi : ∀ a : ZMod q, IsUnit a → |piN N q a.val - M| ≤ E) :
    ‖∑ n ∈ Finset.Icc 1 N, (primeWeight n : ℂ) * χ (n : ZMod q)‖ ≤ q * E := by
  have hsum : (∑ a : ZMod q, χ a * M) = 0 := by
    rw [← Finset.sum_mul, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]
  rw [prime_character_prefix_eq]
  have he : (∑ a : ZMod q, χ a * (piN N q a.val : ℝ)) =
      ∑ a : ZMod q, χ a * ((piN N q a.val : ℂ) - M) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
  rw [he]
  calc _ ≤ ∑ a : ZMod q, ‖χ a * ((piN N q a.val : ℂ) - M)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, E := by
      refine Finset.sum_le_sum fun a _ => ?_
      by_cases ha : IsUnit a
      · rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (hpi a ha) (norm_nonneg _)).trans
          (mul_le_of_le_one_left hE (χ.norm_le_one _))
      · rw [MulChar.map_nonunit χ ha]
        simpa using hE
    _ = q * E := by simp

/-- P0069 page 3 display 1.8, the nonprincipal prime term of page 51.
The existing lab Bombieri Vinogradov theorem bounds every reduced residue class.
The character main term vanishes by orthogonality. -/
theorem character_prime_prefix_bound (D : ℝ) (hD : 0 < D) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q →
        (q : ℝ) ≤ Real.sqrt X / Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ u : ℝ, 0 ≤ u → u ≤ X →
          ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q)‖ ≤
            (q : ℝ) * (K * X / Real.log X ^ D) := by
  obtain ⟨B, hB, K0, h0⟩ := bvPi D hD
  let K := max K0 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨B, hB, K, hK, fun X hX q _ hq hqX χ hχ u hu huX => ?_⟩
  have hE : 0 ≤ K * X / Real.log X ^ D := by
    have : 0 < Real.log X := Real.log_pos (by linarith)
    positivity
  apply prime_character_error_bound χ hχ ⌊u⌋₊ (liD u / q.totient) _ hE
  intro a ha
  have hcop : Nat.Coprime a.val q := (ZMod.isUnit_iff_coprime a.val q).mp
    (by simpa only [ZMod.natCast_zmod_val] using ha)
  let ar : ℕ → ℕ := fun r => if r = q then a.val else 1
  have har : ∀ r : ℕ, Nat.Coprime (ar r) r := by
    intro r
    by_cases hr : r = q
    · subst r
      simpa only [ar, ite_eq_left rfl] using hcop
    · simpa only [ar, ite_eq_right hr] using Nat.coprime_one_left r
  have hsum := h0 X hX ar har (fun _ => u) (fun _ => ⟨hu, huX⟩)
  have hmem : q ∈ Finset.Icc 1 ⌊Real.sqrt X / Real.log X ^ B⌋₊ :=
    Finset.mem_Icc.mpr ⟨hq, Nat.le_floor hqX⟩
  have hsingle := Finset.single_le_sum
    (f := fun r => |LeanLab.PNTPort.BVMax.piAP u r (ar r) - liD u / r.totient|)
    (fun _ _ => abs_nonneg _) hmem
  have hb : |piN ⌊u⌋₊ q a.val - liD u / q.totient| ≤ K0 * X / Real.log X ^ D := by
    simpa only [LeanLab.PNTPort.BVMax.piAP, ar, ite_eq_left rfl] using hsingle.trans hsum
  exact hb.trans (by
    have hscale : 0 ≤ X / Real.log X ^ D := by
      have : 0 < Real.log X := Real.log_pos (by linarith)
      positivity
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_right (le_max_left K0 1) hscale)

/-- P0069 page 3 display 1.8 and the scale Y. A polylogarithmic modulus
lies inside the existing prime distribution cutoff at the ambient scale twice Y. -/
theorem short_scale_cutoff {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (A B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → 2 ≤ x ∧ 2 ≤ 2 * x ^ (11 / 20 + ε) ∧
      Real.log x ^ A ≤ Real.sqrt (2 * x ^ (11 / 20 + ε)) /
        Real.log (2 * x ^ (11 / 20 + ε)) ^ B ∧
      Real.log x / 2 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (A + B)
    (by norm_num : (0 : ℝ) < 1/4)).bound
      (show (0 : ℝ) < 1 / (2 : ℝ) ^ B by positivity)
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp
    (h.and (Filter.eventually_ge_atTop (2 : ℝ)))
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨hb, hx2⟩ := hC x hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hα : (1/2 : ℝ) ≤ 11/20 + ε := by linarith
  have hα1 : 11/20 + ε ≤ (1 : ℝ) := by norm_num at hε8 ⊢; linarith
  have hY : 1 ≤ x ^ (11/20 + ε) := Real.one_le_rpow hx1 (by linarith)
  have hX2 : 2 ≤ 2 * x ^ (11/20 + ε) := by linarith
  have he : Real.log (2 * x ^ (11/20 + ε)) =
      Real.log 2 + (11/20 + ε) * Real.log x := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne',
      Real.log_rpow hx0]
  have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hl2x : Real.log (2 : ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hloglow : Real.log x / 2 ≤ Real.log (2 * x ^ (11/20 + ε)) := by
    rw [he]; nlinarith
  have hlogup : Real.log (2 * x ^ (11/20 + ε)) ≤ 2 * Real.log x := by
    rw [he]; nlinarith
  have hlogX : 0 < Real.log (2 * x ^ (11/20 + ε)) :=
    Real.log_pos (by linarith)
  have hsqrt : x ^ (1/4 : ℝ) ≤ Real.sqrt (2 * x ^ (11/20 + ε)) := by
    calc x ^ (1/4 : ℝ) = Real.sqrt (x ^ (1/2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
          norm_num
      _ ≤ Real.sqrt (x ^ (11/20 + ε)) := Real.sqrt_le_sqrt
          (Real.rpow_le_rpow_of_exponent_le hx1 hα)
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hlog _),
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hb
  have hpow : Real.log x ^ A * Real.log (2 * x ^ (11/20 + ε)) ^ B ≤
      Real.sqrt (2 * x ^ (11/20 + ε)) := by
    calc _ ≤ Real.log x ^ A * (2 * Real.log x) ^ B :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hlogX.le hlogup hB.le) (Real.rpow_nonneg hlog.le _)
      _ = (2 : ℝ) ^ B * Real.log x ^ (A+B) := by
          rw [Real.mul_rpow (by norm_num) hlog.le, Real.rpow_add hlog]
          ring
      _ ≤ (2 : ℝ) ^ B * (1 / (2 : ℝ) ^ B * x ^ (1/4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = x ^ (1/4 : ℝ) := by field_simp
      _ ≤ _ := hsqrt
  exact ⟨hx2, hX2, (le_div_iff₀ (Real.rpow_pos_of_pos hlogX _)).mpr hpow, hloglow⟩

/-- P0069 page 3 display 1.8. Moving from the log of twice Y to log x
costs at most two to power twice A after the modulus log power is absorbed. -/
theorem log_power_quotient {L H A q : ℝ} (hL : 0 < L) (hA : 0 < A)
    (hH : L / 2 ≤ H) (hq : q ≤ L ^ A) :
    q / H ^ (2 * A) ≤ (2 : ℝ) ^ (2 * A) * L ^ (-A) := by
  have hH0 : 0 < H := by linarith
  have hbase : 0 < L / 2 := by positivity
  have hden : (L / 2) ^ (2 * A) ≤ H ^ (2 * A) :=
    Real.rpow_le_rpow hbase.le hH (by positivity)
  calc q / H ^ (2*A) ≤ L ^ A / H ^ (2*A) :=
        div_le_div_of_nonneg_right hq (by positivity)
    _ ≤ L ^ A / (L/2) ^ (2*A) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [Real.div_rpow hL.le (by norm_num), show 2*A = A+A by ring,
        Real.rpow_add hL, Real.rpow_neg hL.le]
      field_simp

/-- P0069 page 3 display 1.8 and page 51 display 5.17, the ordinary prime term.
Every nonprincipal prime character prefix on J has arbitrary logarithmic saving.
This uses the existing lab prime distribution theorem and no rough number estimate. -/
theorem nonprincipal_prime_short {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (primeWeight m : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨B, hB, K, hK, hprefix⟩ := character_prime_prefix_bound (2*A) (by positivity)
  obtain ⟨C0, h0⟩ := short_scale_cutoff hε hε8 A B hB
  let C := max (max C0 (4 * K * (2 : ℝ) ^ (2*A))) 2
  have h0C : C0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hKC : 4 * K * (2 : ℝ) ^ (2*A) ≤ C :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hC2 : 2 ≤ C := le_max_right _ _
  refine ⟨C, fun x hx q hq hqA χ hχ t ht => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨hx2, hX2, hcut, hloglow⟩ := h0 x (h0C.trans hx)
  have hx0 : 0 < x := by linarith
  have hY : 0 < x ^ (11/20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log (2 * x ^ (11/20 + ε)) := Real.log_pos (by linarith)
  have hscale : 0 ≤ x ^ (11/20 + ε) * Real.log x ^ (-A) := by positivity
  by_cases htY : t ≤ x ^ (11/20 + ε)
  · have he : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hmJ, hmt⟩ := Finset.mem_filter.mp hm
      have hmgt := (Finset.mem_Ioc.mp hmJ).1
      have hmle := Nat.le_floor (hmt.trans htY)
      omega
    rw [he, Finset.sum_empty, norm_zero]
    simpa only [mul_assoc] using mul_nonneg (by linarith : (0 : ℝ) ≤ C) hscale
  have hYt : x ^ (11/20 + ε) ≤ t := (lt_of_not_ge htY).le
  have ht0 : 0 ≤ t := hY.le.trans hYt
  have hfloor : ⌊x ^ (11/20 + ε)⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hYt
  have htu : ⌊t⌋₊ ≤ ⌊2 * x ^ (11/20 + ε)⌋₊ := Nat.floor_le_floor ht
  have hfilter : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) =
      Finset.Ioc ⌊x ^ (11/20 + ε)⌋₊ ⌊t⌋₊ := by
    ext m
    have hmf : (m : ℝ) ≤ t ↔ m ≤ ⌊t⌋₊ := ⟨Nat.le_floor,
      fun hm => (Nat.cast_le.mpr hm).trans (Nat.floor_le ht0)⟩
    simp only [rightInterval, Finset.mem_filter, Finset.mem_Ioc, hmf]
    omega
  have hi (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsep := Finset.sum_Ioc_consecutive
    (fun n => (primeWeight n : ℂ) * χ (n : ZMod q))
    (Nat.zero_le ⌊x ^ (11/20 + ε)⌋₊) hfloor
  simp only [hi] at hsep
  have hsum : (∑ m ∈ Finset.Ioc ⌊x ^ (11/20 + ε)⌋₊ ⌊t⌋₊,
      (primeWeight m : ℂ) * χ (m : ZMod q)) =
      (∑ m ∈ Finset.Icc 1 ⌊t⌋₊, (primeWeight m : ℂ) * χ (m : ZMod q)) -
      ∑ m ∈ Finset.Icc 1 ⌊x ^ (11/20 + ε)⌋₊,
        (primeWeight m : ℂ) * χ (m : ZMod q) :=
    eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hsep)
  have hp1 := hprefix (2 * x ^ (11/20 + ε)) hX2 q hq (hqA.trans hcut) χ hχ t ht0 ht
  have hp2 := hprefix (2 * x ^ (11/20 + ε)) hX2 q hq (hqA.trans hcut) χ hχ
    (x ^ (11/20 + ε)) hY.le (by linarith)
  rw [hfilter, hsum]
  have hqpow := log_power_quotient hlog hA hloglow hqA
  calc _ ≤ (q : ℝ) * (K * (2 * x ^ (11/20 + ε)) /
          Real.log (2 * x ^ (11/20 + ε)) ^ (2*A)) +
        (q : ℝ) * (K * (2 * x ^ (11/20 + ε)) /
          Real.log (2 * x ^ (11/20 + ε)) ^ (2*A)) :=
      (norm_sub_le _ _).trans (add_le_add hp1 hp2)
    _ = (4 * K * x ^ (11/20 + ε)) *
        ((q : ℝ) / Real.log (2 * x ^ (11/20 + ε)) ^ (2*A)) := by ring
    _ ≤ (4 * K * x ^ (11/20 + ε)) * ((2 : ℝ) ^ (2*A) * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_left hqpow (by positivity)
    _ = (4 * K * (2 : ℝ) ^ (2*A)) * (x ^ (11/20 + ε) * Real.log x ^ (-A)) := by ring
    _ ≤ C * (x ^ (11/20 + ε) * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_right hKC hscale
    _ = _ := by ring

end LeanLab.BHP1997.Prime514
