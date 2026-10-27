/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3 proof, page 9.
The restriction bound and an explicit continuity estimate give a finite large spectrum net.
Together with pigeonhole this proves the four conclusions for a small density margin.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrNet
import LeanLab.Ternary.MMSSpectrum
import LeanLab.Ternary.MMSGridCover
open Finset
namespace LeanLab.Ternary.MMS

theorem exists_large_spectrum_net (K q δ : ℝ) (hK : 0 ≤ K) (hq : 0 < q) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ N : ℕ, 0 < N → ∀ (η ε : ℝ) (f : ℕ → ℝ),
      Prop31Hyp N η ε K q f → η ≤ 1 → ∃ R : Finset ℝ, R.card ≤ k ∧
        ∀ γ : ℝ, δ * N ≤ ‖fhat N f γ‖ →
          ∃ r ∈ R, ∃ t : ℤ, |γ - r - t| ≤ 1 / (30 * N) := by
  let C := 30 + 8 * Real.pi / δ
  let D := C + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; linarith
  have hδq : 0 < (δ / 2) ^ q := Real.rpow_pos_of_pos (by positivity) _
  let k := ⌈K ^ q * D / (δ / 2) ^ q⌉₊
  refine ⟨k, ?_⟩
  intro N hN η ε f hf hη
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let L := ⌈C * N⌉₊
  have hLlower : C * N ≤ (L : ℝ) := Nat.le_ceil _
  have hLr : (0 : ℝ) < L := lt_of_lt_of_le (mul_pos hC hNr) hLlower
  have hL : 0 < L := by exact_mod_cast hLr
  have hLupper : (L : ℝ) ≤ D * N := by
    have hc := (Nat.ceil_lt_add_one (mul_nonneg hC.le hNr.le)).le
    change (L : ℝ) ≤ C * N + 1 at hc
    dsimp [D]
    nlinarith
  have hL30 : 30 * (N : ℝ) ≤ L := by
    have hterm : 0 ≤ 8 * Real.pi / δ := by positivity
    dsimp [C] at hLlower
    nlinarith
  have hprecision : 1 / (L : ℝ) ≤ 1 / (30 * N) :=
    one_div_le_one_div_of_le (by positivity) hL30
  have hscale : 8 * Real.pi * N ≤ δ * L := by
    have hm := mul_le_mul_of_nonneg_left hLlower hδ.le
    have he : δ * (C * N) = 30 * δ * N + 8 * Real.pi * N := by
      dsimp [C]
      field_simp
    rw [he] at hm
    nlinarith
  have hwidth : 1 / (L : ℝ) ≤ δ / (8 * Real.pi * N) :=
    (div_le_div_iff₀ hLr (by positivity)).mpr (by nlinarith)
  let T : Set ℝ := Set.Icc 0 1 ∩ {γ | δ * N ≤ ‖fhat N f γ‖}
  obtain ⟨R, hRT, hcost, hcover⟩ := exists_grid_spectrum_cover
    (fun γ => ‖fhat N f γ‖) (continuous_fhat N f).norm (fun _ => norm_nonneg _)
    T (fun γ hγ => hγ.1) hL (A := δ * N / 2) (by positivity) hq.le
    (fun γ hγ β hclose =>
      prop31Hyp_near_large_frequency hf hη hN hδ.le γ β hγ.2 (hclose.trans hwidth))
  have hi0 : 0 ≤ ∫ γ in (0 : ℝ)..1, ‖fhat N f γ‖ ^ q :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hmoment := prop31Hyp_moment_le hf hN hK hq
  have hNq : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNr _
  have hAq : (δ * N / 2) ^ q = (δ / 2) ^ q * (N : ℝ) ^ q := by
    rw [show δ * N / 2 = δ / 2 * N by ring, Real.mul_rpow (by positivity) hNr.le]
  have hexp : (N : ℝ) ^ (q - 1) * N = (N : ℝ) ^ q := by
    calc
      (N : ℝ) ^ (q - 1) * N = (N : ℝ) ^ (q - 1) * (N : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((q - 1) + 1) := (Real.rpow_add hNr _ _).symm
      _ = _ := by congr 1; ring
  have hcost' : (R.card : ℝ) * (δ / 2) ^ q * (N : ℝ) ^ q ≤ K ^ q * D * (N : ℝ) ^ q := by
    calc _ = (R.card : ℝ) * (δ * N / 2) ^ q := by rw [hAq]; ring
      _ ≤ (L : ℝ) * (∫ γ in (0 : ℝ)..1, ‖fhat N f γ‖ ^ q) := hcost
      _ ≤ (D * N) * (K ^ q * (N : ℝ) ^ (q - 1)) :=
        mul_le_mul hLupper hmoment hi0 (by positivity)
      _ = K ^ q * D * ((N : ℝ) ^ (q - 1) * N) := by ring
      _ = _ := by rw [hexp]
  have hcancel : (R.card : ℝ) * (δ / 2) ^ q ≤ K ^ q * D :=
    (mul_le_mul_iff_left₀ hNq).mp hcost'
  have hcard : R.card ≤ k := by
    have hbound : (R.card : ℝ) ≤ K ^ q * D / (δ / 2) ^ q :=
      (le_div_iff₀ hδq).mpr hcancel
    have hceil : K ^ q * D / (δ / 2) ^ q ≤ (k : ℝ) := Nat.le_ceil _
    exact_mod_cast hbound.trans hceil
  refine ⟨R, hcard, ?_⟩
  intro γ hγ
  have hfract : fhat N f (Int.fract γ) = fhat N f γ := by
    have hp := (fhat_periodic N f).sub_int_mul_eq (x := γ) ⌊γ⌋
    simpa only [mul_one, Int.fract] using hp
  have hγT : Int.fract γ ∈ T := by
    exact ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, by change δ * N ≤ ‖fhat N f (Int.fract γ)‖; rw [hfract]; exact hγ⟩
  obtain ⟨r, hr, hd⟩ := hcover _ hγT
  refine ⟨r, hr, ⌊γ⌋, ?_⟩
  have he : γ - r - (⌊γ⌋ : ℝ) = Int.fract γ - r := by rw [Int.fract]; ring
  rw [he]
  exact hd.trans hprecision

theorem lemma43_small_density {ε K q δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) (hK : 0 ≤ K) (hq : 0 < q) (hδ : 0 < δ) :
    ∃ C ≥ (0 : ℝ), ∀ η : ℝ, 0 < η → η < 1 → ∀ N : ℕ, 1 ≤ N → ∀ f : ℕ → ℝ,
      Prop31Hyp N η ε K q f → ∃ g h : ℤ →₀ ℝ, Lemma43Data N η ε K q δ C f g h := by
  obtain ⟨k, hk⟩ := exists_large_spectrum_net K q δ hK hq hδ
  apply lemma43_of_frequency_nets hε hε1 hq.le hδ
  refine ⟨k, ?_⟩
  intro η hη hη1 N hN f hf
  exact hk N (by omega) η ε f hf hη1.le

end LeanLab.Ternary.MMS
