/-
P0076 J. Teräväinen, arXiv 1611.08585: Proposition 5.1, page 18, on both ranges `n ∼ N/3` and
`N/3 < n < N/2`, with Lemma 7.1, page 29, read in the slot order of the paper. In
Prop51Split1122b.lean the call of `Lemma71Adapted` inside `Lemma71Choice` and `Display71On` puts
`A (3C)^C` in the threshold slot and `A` in the denominator slot, which is the reverse of the paper;
Lemma71Choice1122d.lean refutes that form and proves the paper form `lemma71_choice_paper`.
Here `Display71OnP` and `Hyp64ExpP` carry the paper order, the reduction of pages 29 to 30 and the
deduction of display 7.1 are rerun on them, and Proposition 5.1 follows from
`lemma71_choice_paper`, `thm65_range`, the new LEAF `hyp64_exp_paper` and
`singular_series_lower_proved`.
burst-20261122 step prop51_paper1122d. AI wrote the Lean code. The binary Goldbach conjecture is
OPEN.
-/
import LeanLab.Teravainen2016.Lemma71Choice1122d
import LeanLab.Teravainen2016.Display71Split1122d
import LeanLab.Teravainen2016.SingularLower1122d

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Lemma 7.1, page 29, in the slot order of the paper: threshold `(log N)^A`, denominators up
to `N/(log N)^{100 B}` with `B = A (3C)^C`, and `Q ≤ (log N)^B`. It corrects the slot order of
`Lemma71Choice`; its proof is `lemma71_choice_paper` of Lemma71Choice1122d.lean. -/
def Lemma71ChoiceP : Prop :=
  ∀ (C A : ℕ) (W : ℤ), 1 ≤ W → ∃ N₀ : ℕ, ∀ α : Fin C → ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ Real.log N ^ (A * (3 * C) ^ C) ∧
      Lemma71Adapted α W N A (A * (3 * C) ^ C) Q

theorem lemma71ChoiceP_holds : Lemma71ChoiceP := lemma71_choice_paper

/-- Display 7.1, page 30, on the summation range `R N`, for every `Q` that Lemma 7.1 allows, as
`Display71On` but with the call of `Lemma71Adapted` in the slot order of the paper: threshold
exponent `A` and denominator exponent `A (3C)^C`. It corrects the slot order of `Display71On`. -/
def Display71OnP (R : ℕ → Finset ℕ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ Cc : ℕ, ∃ A : ℕ, ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) →
    ∀ (c : Fin Cc → ℂ) (α : Fin Cc → ℝ), (∀ k, ‖c k‖ ≤ Cc) →
      (∀ n : ℤ, (χ n : ℂ) = ∑ k, c k * eC (α k * n)) →
    ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    Lemma71Adapted α (WW J w) N A (A * (3 * Cc) ^ Cc) Q →
    ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b →
    ∀ t : ℤ, |(t : ℝ)| ≤ 5 * (N : ℝ) / 3 → ∀ c₀ ∈ QRes Q (WW J w) b,
      δ₀ * singularS ((Q : ℤ) * WW J w) (WW J w * c₀ + b) *
          (∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) - ε * N / Q) ≤
        Real.log ((N : ℝ) / (3 * Q)) ^ ((3 : ℝ) / 2) *
          ∑ n ∈ ((R N).filter (fun n : ℕ => Good (WW J w * (n : ℤ) + b))).filter
            (fun n => n % Q = c₀), χ (t - n)

/-- Hypothesis 6.4, page 22, for `e(ξ m)` with `ξ = Q α` as in 7.3, page 30, as `Hyp64Exp` but
with the call of `Lemma71Adapted` in the slot order of the paper: threshold exponent `A` and
denominator exponent `A (3C)^C`. It corrects the slot order of `Hyp64Exp`. -/
def Hyp64ExpP : Prop :=
  ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ Cc : ℕ, ∃ A : ℕ, ∀ J w : ℕ, 5 ≤ J →
    wBig ≤ w → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q →
    (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    ∀ α : ℝ, Lemma71Adapted (fun _ : Fin 1 => α) (WW J w) N A (A * (3 * Cc) ^ Cc) Q →
    ∀ b : ℤ, Amenable (WW J w) b → ∀ c₀ ∈ QRes Q (WW J w) b,
    ∀ M : Finset ℕ, (∀ m ∈ M, (N : ℝ) / (3 * Q) - 1 < m ∧ (m : ℝ) ≤ 2 * ((N : ℝ) / (3 * Q))) →
      (∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ → m ∈ M) →
    Hyp64 (1 / 2 - 10 * η) (3 / 7 - 10 * η) (3 + η) ((N : ℝ) / (3 * Q)) ((Q : ℤ) * WW J w)
      (WW J w * c₀ + b) M (fun m => eC (-((Q : ℝ) * α) * m))
      (((N : ℝ) / (3 * Q)) / Real.log ((N : ℝ) / (3 * Q)) ^ 199)

/-- LEAF: Hypothesis 6.4 for e(xi m) with xi as in 7.3, page 30, with the approximations of
Lemma 7.1 in the slot order of the paper, proved in Section 10: major arcs in Subsections 10.1 to
10.3, minor arcs in Subsections 10.4 and 10.5, from Lemmas 8.1, 8.2, 9.1 and 9.2. Class HARD. -/
theorem hyp64_exp_paper : Hyp64ExpP := by sorry

/-- Proposition 5.1 on `R` from Lemma 7.1 in the paper order, display 7.1 in the paper order and
the singular series comparison: the reduction on pages 29 to 30. -/
theorem prop51On_of_display71P (R : ℕ → Finset ℕ) (h71 : Lemma71ChoiceP) (hD : Display71OnP R)
    (hS : SingularLower) : Prop51On R := by
  obtain ⟨δ₀, hδ₀, H71⟩ := hD
  obtain ⟨cS, hcS, HS⟩ := hS
  refine ⟨δ₀ * cS, mul_pos hδ₀ hcS, ?_⟩
  intro Cc
  obtain ⟨A, HA⟩ := H71 Cc
  set B : ℕ := A * (3 * Cc) ^ Cc with hB
  refine ⟨B, ?_⟩
  intro J w hJ hw hCw ε hε
  obtain ⟨N₀, HN⟩ := HA J w hJ hw hCw ε hε
  have hW1 : (1 : ℤ) ≤ WW J w := WW_pos' J w
  obtain ⟨N₁, HL⟩ := h71 Cc A (WW J w) hW1
  obtain ⟨N₂, HE⟩ := eventually_log_rpow_le_sqrt 3 (B : ℝ)
  refine ⟨max (max N₀ N₁) (max N₂ 1), ?_⟩
  intro χ hχ0 hχC N hN
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨c, α, hc, hrep⟩ := hχC
  obtain ⟨Q, hQ1, hQB, hAd⟩ := HL α N hN1
  refine ⟨Q, hQ1, hQB, ?_⟩
  intro b hb0 hbW hamen t ht c₀ hc₀
  have h := HN χ hχ0 c α hc hrep N hN0 Q hQ1 hQB hAd b hb0 hbW hamen t ht c₀ hc₀
  have hs := HS J w hJ hw b hamen Q hQ1 c₀ hc₀
  set W : ℤ := WW J w with hWdef
  set S : ℝ := singularS ((Q : ℤ) * W) (W * c₀ + b) with hSdef
  set X : ℝ := ∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) - ε * N / Q with hX
  set G : ℝ := ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
      (fun n => n % Q = c₀), χ (t - n) with hG
  set r : ℝ := (Q : ℝ) / #(QRes Q W b) with hr
  set φ : ℝ := (Nat.totient W.toNat : ℝ) with hφ
  have hG0 : 0 ≤ G := sum_nonneg (fun n _ => hχ0 _)
  have hr0 : 0 ≤ r := by positivity
  have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
  have hφ0 : 0 < φ := by
    have : 0 < W.toNat := by omega
    have h' : 0 < Nat.totient W.toNat := Nat.totient_pos.mpr this
    show (0 : ℝ) < (Nat.totient W.toNat : ℝ)
    exact_mod_cast h'
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN3
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  -- `1 ≤ x = N / (3 Q) ≤ N`
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have h3Q : 3 * (Q : ℝ) ≤ N := by
    have e := HE N hN2
    rw [Real.rpow_natCast] at e
    have hsq : Real.sqrt N ≤ N := by
      have h1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hNr
      have := Real.mul_self_sqrt (show (0 : ℝ) ≤ N by linarith)
      nlinarith
    linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) / (3 * Q) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hxN : (N : ℝ) / (3 * Q) ≤ N := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hlogx0 : 0 ≤ Real.log ((N : ℝ) / (3 * Q)) := Real.log_nonneg hx1
  have hlogxN : Real.log ((N : ℝ) / (3 * Q)) ≤ Real.log N :=
    Real.log_le_log (by linarith) hxN
  have hpow : Real.log ((N : ℝ) / (3 * Q)) ^ ((3 : ℝ) / 2) ≤ Real.log N ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hlogx0 hlogxN (by norm_num)
  -- `(φ/W)^{3/2} (W/φ)^{3/2} = 1`
  set Φ : ℝ := (φ / W) ^ ((3 : ℝ) / 2) with hΦ
  set P : ℝ := ((W : ℝ) / φ) ^ ((3 : ℝ) / 2) with hP
  have hΦ0 : 0 ≤ Φ := Real.rpow_nonneg (by positivity) _
  have hΦP : Φ * P = 1 := by
    rw [hΦ, hP, ← Real.mul_rpow (by positivity) (by positivity)]
    rw [show φ / (W : ℝ) * ((W : ℝ) / φ) = 1 by field_simp]
    exact Real.one_rpow _
  show δ₀ * cS * r * X ≤ Real.log N ^ ((3 : ℝ) / 2) * Φ * G
  rcases le_or_gt X 0 with hX0 | hX0
  · have h1 : δ₀ * cS * r * X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hX0
    have h2 : 0 ≤ Real.log N ^ ((3 : ℝ) / 2) * Φ * G := by
      have := Real.rpow_nonneg hlogN ((3 : ℝ) / 2)
      positivity
    linarith
  · have hs' : cS * P * r ≤ S := hs
    have e1 : δ₀ * cS * r * X = Φ * (δ₀ * (cS * P * r) * X) := by
      calc δ₀ * cS * r * X = (Φ * P) * (δ₀ * cS * r * X) := by rw [hΦP, one_mul]
        _ = Φ * (δ₀ * (cS * P * r) * X) := by ring
    have e2 : δ₀ * (cS * P * r) * X ≤ δ₀ * S * X := by
      apply mul_le_mul_of_nonneg_right _ hX0.le
      exact mul_le_mul_of_nonneg_left hs' hδ₀.le
    have e3 : δ₀ * S * X ≤ Real.log N ^ ((3 : ℝ) / 2) * G :=
      le_trans h (mul_le_mul_of_nonneg_right hpow hG0)
    rw [e1]
    calc Φ * (δ₀ * (cS * P * r) * X) ≤ Φ * (Real.log N ^ ((3 : ℝ) / 2) * G) :=
          mul_le_mul_of_nonneg_left (le_trans e2 e3) hΦ0
      _ = Real.log N ^ ((3 : ℝ) / 2) * Φ * G := by ring

/-- Display 7.1 in the paper order on `R` from Theorem 6.5, Hypothesis 6.4 for `e(ξ m)` in the
paper order and the amenability of `L`: the deduction on page 30. -/
theorem display71OnP_of_leaves (R : ℕ → Finset ℕ) (hR : RShape R) (hT : Thm65Range)
    (hH : Hyp64ExpP)
    (hAm : ∀ (W b : ℤ) (Q c₀ : ℕ), Amenable W b → 1 ≤ Q → c₀ ∈ QRes Q W b →
      Amenable ((Q : ℤ) * W) (W * c₀ + b)) : Display71OnP R := by
  obtain ⟨δ₀, hδ₀, η₀, hη₀, T⟩ := hT
  obtain ⟨η₁, hη₁, H⟩ := hH
  set η : ℝ := min η₀ η₁ with hη
  have hη0 : 0 < η := lt_min hη₀ hη₁
  refine ⟨δ₀, hδ₀, fun Cc => ?_⟩
  obtain ⟨A, HA⟩ := H η hη0 (min_le_right _ _) Cc
  refine ⟨A, ?_⟩
  intro J w hJ hw hCw ε hε
  set B : ℕ := A * (3 * Cc) ^ Cc with hB
  set W : ℤ := WW J w with hWdef
  have hW1 : (1 : ℤ) ≤ W := WW_pos' J w
  obtain ⟨N₁, HN1⟩ := HA J w hJ hw
  obtain ⟨X₀, HX⟩ := T η hη0 (min_le_left _ _) B ((W : ℝ) * 3 ^ B) ((Cc : ℝ) * Cc) (3 * ε)
    (by positivity)
  obtain ⟨N₂, HN2⟩ := d71_scale B W hW1 (max X₀ 1) ((Cc : ℝ) * Cc) (3 * ε) (by positivity)
  refine ⟨max N₁ N₂, ?_⟩
  intro χ hχ0 c α hc hrep N hN Q hQ1 hQB hAd b hb0 hbW hamen t ht c₀ hc₀
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  have hc₀Q : c₀ < Q := by
    have := (Finset.mem_filter.mp hc₀).1
    exact Finset.mem_range.mp this
  obtain ⟨hXY', hK, hBd⟩ := HN2 N hN2 Q hQ1 hQB
  have hXY := le_trans (le_max_left _ _) hXY'
  have hX1 := le_trans (le_max_right _ _) hXY'
  set X : ℝ := (N : ℝ) / (3 * Q) with hX
  set M : Finset ℕ := ((R N).filter (fun n => n % Q = c₀)).image (fun n => n / Q) with hM
  obtain ⟨hMb, hMc⟩ := d71_image_bounds R hR N Q c₀ hQ1 hc₀Q
  set ω : ℕ → ℝ := fun m => χ (t - ((Q * m + c₀ : ℕ) : ℤ)) with hω
  -- the bound `|χ| ≤ C²`
  have hχC : ∀ n : ℤ, χ n ≤ (Cc : ℝ) * Cc := by
    intro n
    have h1 : ‖(χ n : ℂ)‖ ≤ ∑ k, ‖c k * eC (α k * n)‖ := by
      rw [hrep n]; exact norm_sum_le _ _
    have h2 : ∑ k, ‖c k * eC (α k * n)‖ ≤ ∑ _k : Fin Cc, (Cc : ℝ) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [norm_mul, d71_eC_norm, mul_one]; exact hc k
    have h3 : ∑ _k : Fin Cc, (Cc : ℝ) = (Cc : ℝ) * Cc := by simp
    have h4 : χ n ≤ ‖(χ n : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    linarith
  -- the expansion of `ω_m` by (2.2)
  have hωexp : ∀ m : ℕ, ((ω m : ℝ) : ℂ) =
      ∑ k, (c k * eC (α k * ((t : ℝ) - c₀))) * eC (-((Q : ℝ) * α k) * m) := by
    intro m
    simp only [hω]
    rw [hrep]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_assoc, ← d71_eC_add]
    congr 2
    push_cast
    ring
  -- Hypothesis 6.4 for `ω`
  have hHyp : Hyp64 (1 / 2 - 10 * η) (3 / 7 - 10 * η) (3 + η) X ((Q : ℤ) * W) (W * c₀ + b) M
      (fun m => (ω m : ℂ)) (3 * ε * X / Real.log X ^ 100) := by
    have hcombo := hyp64_combo Finset.univ (1 / 2 - 10 * η) (3 / 7 - 10 * η) (3 + η) X
      ((Q : ℤ) * W) (W * c₀ + b) M (fun k => c k * eC (α k * ((t : ℝ) - c₀)))
      (fun k m => eC (-((Q : ℝ) * α k) * m)) (X / Real.log X ^ 199)
      (fun k _ => HN1 N hN1 Q hQ1 hQB (α k) (fun _ => hAd k) b hamen c₀ hc₀ M hMb hMc)
    have hfun : (fun m => (ω m : ℂ)) = (fun n : ℕ => ∑ k, (c k * eC (α k * ((t : ℝ) - c₀))) *
        eC (-((Q : ℝ) * α k) * n)) := funext hωexp
    have hsum : (∑ k, ‖c k * eC (α k * ((t : ℝ) - c₀))‖) ≤ (Cc : ℝ) * Cc := by
      have : ∑ k, ‖c k * eC (α k * ((t : ℝ) - c₀))‖ ≤ ∑ _k : Fin Cc, (Cc : ℝ) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [norm_mul, d71_eC_norm, mul_one]; exact hc k
      simpa using this
    have hX0 : 0 ≤ X / Real.log X ^ 199 := by
      have := Real.log_nonneg hX1
      positivity
    rw [hfun]
    refine ⟨fun g hg => le_trans (hcombo.1 g hg) ?_, le_trans hcombo.2 ?_⟩
    · exact le_trans (mul_le_mul_of_nonneg_right hsum hX0) hBd
    · exact le_trans (mul_le_mul_of_nonneg_right hsum hX0) hBd
  have hmain := HX X hXY ((Q : ℤ) * W) (W * c₀ + b) (hAm W b Q c₀ hamen hQ1 hc₀) hK M hMb hMc
    ω (fun m => hχ0 _) (fun m => hχC _) hHyp
  -- reindexing
  have e1 : ∑ m ∈ M, ω m = ∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) := by
    have := d71_reindex (R N) Q c₀ hc₀Q (fun n => χ (t - n))
    simpa [hω, hM] using this
  have e2 : ∑ m ∈ M.filter (fun m : ℕ => Good ((Q : ℤ) * W * m + (W * c₀ + b))), ω m =
      ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
        (fun n => n % Q = c₀), χ (t - n) := by
    rw [Finset.filter_comm, Finset.sum_filter, Finset.sum_filter]
    have := d71_reindex (R N) Q c₀ hc₀Q
      (fun n => if Good (W * (n : ℤ) + b) then χ (t - n) else 0)
    rw [← this, hM]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have harg : (Q : ℤ) * W * m + (W * c₀ + b) = W * (((Q * m + c₀ : ℕ)) : ℤ) + b := by
      push_cast; ring
    simp only [hω, harg]
  have e3 : 3 * ε * X = ε * N / Q := by
    rw [hX]; field_simp
  rw [e2, e1, e3] at hmain
  exact hmain

/-- Proposition 5.1 for `n ∼ N/3`, the statement of `prop51_dyad`, from `lemma71_choice_paper`,
`thm65_range`, `hyp64_exp_paper` and `singular_series_lower_proved`. -/
theorem prop51_dyad_paper : type_of% @LeanLab.Teravainen2016.prop51_dyad :=
  prop51On_of_display71P dyad lemma71_choice_paper
    (display71OnP_of_leaves dyad rshape_dyad thm65_range hyp64_exp_paper
      (fun W b Q c₀ hA hQ hc => amenable_QW W b Q c₀ hA hQ hc))
    SingularLower1122d.singular_series_lower_proved

/-- Proposition 5.1 for `N/3 < n < N/2`, the statement of `prop51_half`, from the same inputs. -/
theorem prop51_half_paper : type_of% @LeanLab.Teravainen2016.prop51_half :=
  prop51On_of_display71P half lemma71_choice_paper
    (display71OnP_of_leaves half rshape_half thm65_range hyp64_exp_paper
      (fun W b Q c₀ hA hQ hc => amenable_QW W b Q c₀ hA hQ hc))
    SingularLower1122d.singular_series_lower_proved

end LeanLab.Teravainen2016

#print axioms LeanLab.Teravainen2016.prop51On_of_display71P
#print axioms LeanLab.Teravainen2016.display71OnP_of_leaves
#print axioms LeanLab.Teravainen2016.prop51_dyad_paper
#print axioms LeanLab.Teravainen2016.prop51_half_paper
