/-
Baker, Harman and Pintz 1997, pages 2 and 3, unit U-1609. Ordered short weights have ordered
densities: condition ii at the trivial character, q = 1, t = 2x^{11/20+ε}, with a log saving A = 2.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165
namespace LeanLab.BHP1997.DecompC165b
open Classical Complex

theorem right_density_mono {ε B0 B1 v0 v1 : ℝ} {b0 b1 : ℝ → ℕ → ℝ} (hε : 0 < ε)
    (h0 : RightConditions ε B0 v0 b0) (h1 : RightConditions ε B1 v1 b1)
    (hs : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, b0 x m ≤ b1 x m) : v0 ≤ v1 := by
  by_contra hcon
  have hδ : 0 < v0 - v1 := by linarith [not_le.mp hcon]
  obtain ⟨X, hX⟩ := hs
  obtain ⟨C0, hC0⟩ := h0.2.1 2 (by norm_num)
  obtain ⟨C1, hC1⟩ := h1.2.1 2 (by norm_num)
  set θ : ℝ := 11 / 20 + ε with hθ
  have hθ0 : 0 < θ := by positivity
  set K : ℝ := |C0| + |C1| + 1 with hK
  have hK0 : 0 < K := by positivity
  set Y : ℝ := max (max X (max C0 C1)) (max 4 (Real.exp (4 * θ * K / (v0 - v1) + 1))) with hY
  have hxX : X ≤ Y := (le_max_left _ _).trans (le_max_left _ _)
  have hxC0 : C0 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hxC1 : C1 ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hx4 : 4 ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hxe : Real.exp (4 * θ * K / (v0 - v1) + 1) ≤ Y :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hY0 : 0 < Y := by linarith
  have hlogbig : 4 * θ * K / (v0 - v1) + 1 ≤ Real.log Y := by
    have := Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at this
  have hfrac : 0 ≤ 4 * θ * K / (v0 - v1) := by positivity
  have hlog1 : 1 ≤ Real.log Y := by linarith
  have hlogpos : 0 < Real.log Y := by linarith
  set H : ℝ := Y ^ θ with hH
  have hH2 : 2 ≤ H := by
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := h4.symm
      _ ≤ Y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
      _ ≤ Y ^ θ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hθ]; linarith)
  set Λ : ℝ := Real.log H with hΛ
  have hΛv : Λ = θ * Real.log Y := by rw [hΛ, hH, Real.log_rpow hY0]
  have hΛ0 : 0 < Λ := by rw [hΛv]; positivity
  have hχ : ∀ z : ZMod 1, (1 : DirichletCharacter ℂ 1) z = 1 := by
    intro z
    apply MulChar.one_apply
    have hz : z = 1 := Subsingleton.elim _ _
    rw [hz]
    exact isUnit_one
  have hq1 : ((1 : ℕ) : ℝ) ≤ Real.log Y ^ (2 : ℝ) := by
    simpa using Real.one_le_rpow hlog1 (by norm_num : (0 : ℝ) ≤ 2)
  have hrp : Real.log Y ^ (-2 : ℝ) = (Real.log Y ^ 2)⁻¹ := by
    rw [Real.rpow_neg hlogpos.le]
    norm_num
  have mean : ∀ (C v : ℝ) (b : ℝ → ℕ → ℝ),
      ‖∑ m ∈ (rightInterval ε Y).filter (fun m : ℕ => (m : ℝ) ≤ 2 * H),
        ((b Y m : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) -
          Thm2.delta (1 : DirichletCharacter ℂ 1) * v / Real.log H)‖ ≤ C * H * Real.log Y ^ (-2 : ℝ) →
      |∑ m ∈ rightInterval ε Y, (b Y m - v / Λ)| ≤ C * H * (Real.log Y ^ 2)⁻¹ := by
    intro C v b h
    have hfil : (rightInterval ε Y).filter (fun m : ℕ => (m : ℝ) ≤ 2 * H) = rightInterval ε Y := by
      apply Finset.filter_true_of_mem
      intro m hm
      have hm2 := (Finset.mem_Ioc.mp hm).2
      have hnn : 0 ≤ 2 * H := by positivity
      exact (Nat.le_floor_iff hnn).mp hm2
    rw [hfil] at h
    have he : ∑ m ∈ rightInterval ε Y,
        ((b Y m : ℂ) * (1 : DirichletCharacter ℂ 1) (m : ZMod 1) -
          Thm2.delta (1 : DirichletCharacter ℂ 1) * v / Real.log H) =
        ((∑ m ∈ rightInterval ε Y, (b Y m - v / Λ) : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro m _
      rw [hχ]
      simp [Thm2.delta, hΛ]
    rw [he, Complex.norm_real, Real.norm_eq_abs, hrp] at h
    exact h
  have hb0 := mean C0 v0 b0 (hC0 Y hxC0 1 le_rfl hq1 1 (2 * H) le_rfl)
  have hb1 := mean C1 v1 b1 (hC1 Y hxC1 1 le_rfl hq1 1 (2 * H) le_rfl)
  set I := rightInterval ε Y with hI
  have hcard : H / 2 ≤ (I.card : ℝ) := by
    have hc : I.card = ⌊2 * H⌋₊ - ⌊H⌋₊ := by rw [hI, rightInterval, Nat.card_Ioc]
    have hle : ⌊H⌋₊ ≤ ⌊2 * H⌋₊ := Nat.floor_mono (by linarith)
    rw [hc, Nat.cast_sub hle]
    have h1 := Nat.lt_floor_add_one (2 * H)
    have h2 := Nat.floor_le (show 0 ≤ H by linarith)
    linarith
  have hdiff : (v0 - v1) * (I.card : ℝ) / Λ ≤
      (∑ m ∈ I, (b1 Y m - v1 / Λ)) - ∑ m ∈ I, (b0 Y m - v0 / Λ) := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ m ∈ I, (v0 - v1) / Λ ≤ (b1 Y m - v1 / Λ) - (b0 Y m - v0 / Λ) := by
      intro m hm
      have := hX Y hxX m hm
      have he : (v0 - v1) / Λ = v0 / Λ - v1 / Λ := sub_div _ _ _
      linarith
    calc (v0 - v1) * (I.card : ℝ) / Λ = ∑ _m ∈ I, (v0 - v1) / Λ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hA := (le_abs_self _).trans hb1
  have hB := (neg_abs_le _).trans' (neg_le_neg hb0)
  have hsum : (v0 - v1) * (I.card : ℝ) / Λ ≤ (C0 + C1) * H * (Real.log Y ^ 2)⁻¹ := by
    have hexp : (C0 + C1) * H * (Real.log Y ^ 2)⁻¹ =
        C0 * H * (Real.log Y ^ 2)⁻¹ + C1 * H * (Real.log Y ^ 2)⁻¹ := by ring
    linarith
  have hCK : C0 + C1 ≤ K := by
    rw [hK]
    linarith [le_abs_self C0, le_abs_self C1]
  have hHpos : 0 < H := by linarith
  have hinvnn : 0 ≤ (Real.log Y ^ 2)⁻¹ := by positivity
  have h1 : (v0 - v1) * (H / 2) / Λ ≤ K * H * (Real.log Y ^ 2)⁻¹ :=
    calc (v0 - v1) * (H / 2) / Λ ≤ (v0 - v1) * (I.card : ℝ) / Λ := by gcongr
      _ ≤ (C0 + C1) * H * (Real.log Y ^ 2)⁻¹ := hsum
      _ ≤ K * H * (Real.log Y ^ 2)⁻¹ := by gcongr
  rw [hΛv] at h1
  have h2 : (v0 - v1) * Real.log Y ≤ 2 * θ * K := by
    have hne := hlogpos.ne'
    have hthne := hθ0.ne'
    have hHne := hHpos.ne'
    have heq : (v0 - v1) * (H / 2) / (θ * Real.log Y) * (2 * θ * Real.log Y ^ 2 / H) =
        (v0 - v1) * Real.log Y := by
      field_simp
    have heq2 : K * H * (Real.log Y ^ 2)⁻¹ * (2 * θ * Real.log Y ^ 2 / H) = 2 * θ * K := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_right h1
      (show 0 ≤ 2 * θ * Real.log Y ^ 2 / H by positivity)
    rwa [heq, heq2] at hmul
  have h3 : 4 * θ * K ≤ (v0 - v1) * Real.log Y := by
    have hh : 4 * θ * K / (v0 - v1) ≤ Real.log Y := by linarith
    rw [div_le_iff₀ hδ] at hh
    linarith
  have hpos : 0 < θ * K := by positivity
  linarith

end LeanLab.BHP1997.DecompC165b

#print axioms LeanLab.BHP1997.DecompC165b.right_density_mono
