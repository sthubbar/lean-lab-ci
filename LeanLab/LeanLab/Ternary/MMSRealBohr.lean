/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3 proof, page 9.
Pigeonhole gives a large short averaging set for finitely many real frequencies.
Zero is allowed. Only differences and phases are used by the local model.
The covering of the whole large spectrum remains a separate step.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrPhases
open Finset
open scoped Classical
noncomputable section
namespace LeanLab.Ternary.MMS
noncomputable def phaseBucket (K : ℕ) (x : ℝ) : ℕ := ⌊(K : ℝ) * Int.fract x⌋₊

theorem phaseBucket_lt {K : ℕ} (hK : 0 < K) (x : ℝ) : phaseBucket K x < K := by
  unfold phaseBucket
  apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg x))).mpr
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  nlinarith [Int.fract_lt_one x]

theorem phase_close_of_bucket {K : ℕ} (hK : 0 < K) (x y : ℝ)
    (hb : phaseBucket K x = phaseBucket K y) :
    ∃ k : ℤ, |x - y - k| ≤ 1 / (K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hx0 : 0 ≤ (K : ℝ) * Int.fract x := mul_nonneg hKr.le (Int.fract_nonneg x)
  have hy0 : 0 ≤ (K : ℝ) * Int.fract y := mul_nonneg hKr.le (Int.fract_nonneg y)
  have hx1 := Nat.floor_le hx0
  have hx2 := Nat.lt_floor_add_one ((K : ℝ) * Int.fract x)
  have hy1 := Nat.floor_le hy0
  have hy2 := Nat.lt_floor_add_one ((K : ℝ) * Int.fract y)
  unfold phaseBucket at hb
  rw [hb] at hx1 hx2
  refine ⟨⌊x⌋ - ⌊y⌋, ?_⟩
  have he : x - y - ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) = Int.fract x - Int.fract y := by
    rw [Int.fract, Int.fract]
    push_cast
    ring
  rw [he]
  apply (le_div_iff₀ hKr).mpr
  rw [show |Int.fract x - Int.fract y| * (K : ℝ) =
      |(Int.fract x - Int.fract y) * (K : ℝ)| by rw [abs_mul, abs_of_pos hKr], abs_le]
  constructor <;> nlinarith

theorem exists_finite_frequency_bohr (R : Finset ℝ) (M K : ℕ) (hK : 0 < K) :
    ∃ B : Finset ℤ, B.Nonempty ∧
      ((M : ℝ) + 1) / (K : ℝ) ^ R.card ≤ B.card ∧
      (∀ b ∈ B, 0 ≤ b ∧ b ≤ M) ∧
      ∀ γ ∈ R, ∀ b ∈ B, ∃ k : ℤ, |(b : ℝ) * γ - k| ≤ 1 / (K : ℝ) := by
  let φ : ℕ → (↥R → Fin K) := fun n γ =>
    ⟨phaseBucket K ((n : ℝ) * γ.1), phaseBucket_lt hK _⟩
  have hcard : ((univ : Finset (↥R → Fin K)).card : ℝ) = (K : ℝ) ^ R.card := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    push_cast
    rfl
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpow : (0 : ℝ) < (K : ℝ) ^ R.card := by positivity
  obtain ⟨y, hy, hsize⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := range (M + 1)) (t := univ) (f := φ)
    (b := ((M : ℝ) + 1) / (K : ℝ) ^ R.card)
    (fun _ _ => mem_univ _) (show (univ : Finset (↥R → Fin K)).Nonempty from ⟨(fun _ => ⟨0, hK⟩), mem_univ _⟩) (by
      rw [nsmul_eq_mul, hcard, card_range]
      push_cast
      field_simp
      nlinarith)
  let F := (range (M + 1)).filter (fun n => φ n = y)
  have hF : F.Nonempty := by
    apply card_pos.mp
    have hs : (0 : ℝ) < F.card := lt_of_lt_of_le (by positivity) hsize
    exact_mod_cast hs
  let x₀ := F.min' hF
  have hx₀ : x₀ ∈ F := F.min'_mem hF
  let B := F.image (fun x : ℕ => (x : ℤ) - (x₀ : ℤ))
  have hBcard : B.card = F.card := by
    dsimp [B]
    apply card_image_of_injOn
    intro a ha b hb hab
    change (a : ℤ) - x₀ = (b : ℤ) - x₀ at hab
    omega
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, mem_image.mpr ⟨x₀, hx₀, by simp⟩⟩
  · rw [hBcard]
    exact hsize
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    have hxrange : x < M + 1 := mem_range.mp (mem_filter.mp hx).1
    have hmin := F.min'_le x hx
    constructor <;> omega
  · intro γ hγ b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    have hxy : φ x = y := (mem_filter.mp hx).2
    have hx0y : φ x₀ = y := (mem_filter.mp hx₀).2
    have he := congrArg (fun g => (g ⟨γ, hγ⟩ : ℕ)) (hxy.trans hx0y.symm)
    dsimp [φ] at he
    obtain ⟨k, hk⟩ := phase_close_of_bucket hK ((x : ℝ) * γ) ((x₀ : ℝ) * γ) he
    refine ⟨k, ?_⟩
    simpa only [Int.cast_sub, Int.cast_natCast, sub_mul] using hk

theorem exists_bohr_set_of_finite_spectrum (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (R : Finset ℝ), R.card ≤ k →
      ∃ B : Finset ℤ, B.Nonempty ∧ κ * N ≤ B.card ∧
        (∀ b ∈ B, 0 ≤ b ∧ (b : ℝ) ≤ δ * N) ∧
        (∀ a ∈ B, ∀ b ∈ B, |((a - b : ℤ) : ℝ)| ≤ δ * N) ∧
        ∀ γ ∈ R, ∀ b ∈ B, ∃ t : ℤ, |(b : ℝ) * γ - t| ≤ δ / 30 := by
  let K := ⌈30 / δ⌉₊ + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hKlower : 30 / δ ≤ (K : ℝ) := by
    have hc := Nat.le_ceil (30 / δ)
    dsimp [K]
    push_cast
    linarith
  have hphase : 1 / (K : ℝ) ≤ δ / 30 := by
    apply (div_le_div_iff₀ hKr (by norm_num)).mpr
    have hm := (div_le_iff₀ hδ).mp hKlower
    nlinarith
  refine ⟨δ / (K : ℝ) ^ k, by positivity, ?_⟩
  intro N R hR
  let M := ⌊δ * N⌋₊
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hM : (M : ℝ) ≤ δ * N := Nat.floor_le (mul_nonneg hδ.le hN)
  have hM' : δ * N < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  obtain ⟨B, hB, hs, hb, hp⟩ := exists_finite_frequency_bohr R M K hK
  have hpow : (K : ℝ) ^ R.card ≤ (K : ℝ) ^ k :=
    pow_le_pow_right₀ (by exact_mod_cast hK) hR
  refine ⟨B, hB, ?_, ?_, ?_, ?_⟩
  · calc δ / (K : ℝ) ^ k * N = δ * N / (K : ℝ) ^ k := by ring
      _ ≤ ((M : ℝ) + 1) / (K : ℝ) ^ k :=
        div_le_div_of_nonneg_right hM'.le (by positivity)
      _ ≤ ((M : ℝ) + 1) / (K : ℝ) ^ R.card :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ ≤ B.card := hs
  · intro b hbB
    have hbr : (b : ℝ) ≤ M := by exact_mod_cast (hb b hbB).2
    exact ⟨(hb b hbB).1, hbr.trans hM⟩
  · intro a ha b hbB
    have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast (hb a ha).1
    have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast (hb b hbB).1
    have haM : (a : ℝ) ≤ M := by exact_mod_cast (hb a ha).2
    have hbM : (b : ℝ) ≤ M := by exact_mod_cast (hb b hbB).2
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · intro γ hγ b hbB
    obtain ⟨t, ht⟩ := hp γ hγ b hbB
    exact ⟨t, ht.trans hphase⟩

end LeanLab.Ternary.MMS
