import LeanLab.ExceptionalSet.Decomp553b

/-!
A split of the inner mass bound for the derived high index block.

The single inner mass step is cut into two leaves. The first leaf is the
localization of the large phase region: a block phase exceeding the threshold
forces the shift into the finite union of half integer strips. The second leaf
bounds the prime kernel mass over those strips by the same final constant. The
assembly below obtains the target statement from the two leaves, using only the
already proved window parameters of the imported development to supply the
positivity of the truncation width.

No statement of the imported file is changed.
-/
namespace LeanLab.ExceptionalSet.Decomp553b
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF. Step one of the inner mass bound for the high index block: the
localization of the large phase region. If the block phase at the shift `b - a`
is larger than `N` times the negative five sixths power of the truncation
height, then that shift lies in the finite union of half integer strips of
width the one minus `δ` power of the block length. -/
theorem leaf_high_j0_large_phase_strip (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ →
              b ∈ strips (calE γ κ N) (F γ N) δ a := by
  sorry

/-- LEAF. Step two of the inner mass bound for the high index block: the prime
kernel mass carried by the localized strips. Its integral over the truncated
window intersected with the union of strips is at most the final constant. -/
theorem leaf_high_j0_strip_mass (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
              strips (calE γ κ N) (F γ N) δ a,
              mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b) ≤
                6 * C * F γ N * calE γ κ N ^ (-(2 / 3 : ℝ)) := by
  classical
  obtain ⟨δm, hδm, hsup⟩ :=
    LeanLab.ExceptionalSet.UpJ200.MinorSup446.leaf_minor_sup_supplied γ h1 h2
  refine ⟨min δm 1, lt_min hδm one_pos, fun δ hδ hδs => ?_⟩
  have hδm' : δ < δm := hδs.trans_le (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδs.le.trans (min_le_right _ _)
  obtain ⟨C, hC, Nm, hsup⟩ := hsup δ hδ hδm'
  refine ⟨1, one_pos, fun κ hκ _ => ?_⟩
  obtain ⟨Np, hp⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδ1 hκ
  refine ⟨C, hC, max Nm Np, fun N hN => ?_⟩
  have hNm : Nm ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_right _ _).trans hN
  obtain ⟨-, hE1, -, hlog, hscale, hTX, -, -, -⟩ := hp N hNp
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hΔ1 : calE γ κ N ^ (-(5 / 12 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hE1 (by norm_num)
  intro a _
  exact prime_strip_inner (calE γ κ N) (F γ N) C δ hE1.le hX0 hC.le hΔ1 hTX hlog hscale
    (fun b hb => hsup N hNm b hb) a _ Set.inter_subset_left Set.inter_subset_right

/-- The inner mass bound for the high index block, derived from the two leaves
by restricting the integral to the localized strips. -/
theorem leaf_inner_high_j0_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
              {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖},
              mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b) ≤
                6 * C * F γ N * calE γ κ N ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨d₁, hd₁, Hloc⟩ := leaf_high_j0_large_phase_strip γ h1 h2
  obtain ⟨d₂, hd₂, Hstrip⟩ := leaf_high_j0_strip_mass γ h1 h2
  refine ⟨min d₁ (min d₂ 1), lt_min hd₁ (lt_min hd₂ one_pos), ?_⟩
  intro δ hδ hδlt
  have hδ₁ : δ < d₁ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ₂ : δ < d₂ := (lt_of_lt_of_le hδlt (min_le_right _ _)).trans_le (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδlt (min_le_right _ _)).le.trans (min_le_right _ _)
  obtain ⟨k₁, hk₁, Kloc⟩ := Hloc δ hδ hδ₁
  obtain ⟨k₂, hk₂, Kstrip⟩ := Hstrip δ hδ hδ₂
  refine ⟨min k₁ k₂, lt_min hk₁ hk₂, ?_⟩
  intro κ hκ hκlt
  obtain ⟨N₁, HN₁⟩ := Kloc κ hκ (le_trans hκlt (min_le_left _ _))
  obtain ⟨C, hC, N₂, HN₂⟩ := Kstrip κ hκ (le_trans hκlt (min_le_right _ _))
  obtain ⟨N₃, HN₃⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδ1 hκ
  refine ⟨C, hC, max (max N₁ N₂) N₃, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans hN
  have hcalE : 1 < calE γ κ N := (HN₃ N hN₃).2.1
  have hE0 : 0 < calE γ κ N := lt_trans one_pos hcalE
  have hΔ : 0 < calE γ κ N ^ (-(5 / 12 : ℝ)) := Real.rpow_pos_of_pos hE0 _
  have hΔ1 : calE γ κ N ^ (-(5 / 12 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hcalE (by norm_num)
  intro a ha
  have hloc := HN₁ N hN₁
  have hsub : oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
      {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
        ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖} ⊆
      oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
        strips (calE γ κ N) (F γ N) δ a := by
    intro b hb
    exact ⟨hb.1, hloc a ha b hb.1 hb.2⟩
  calc
    (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
        {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
          ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖},
        mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b)
      ≤ (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
          strips (calE γ κ N) (F γ N) δ a,
          mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b) :=
        setIntegral_mono_set (μ := volume)
          ((mass_integrable (F γ N ^ (6 * δ)) (F γ N)
            (calE γ κ N ^ (-(5 / 12 : ℝ))) hΔ hΔ1).integrableOn)
          (Filter.Eventually.of_forall (fun b => norm_nonneg _))
          (Filter.Eventually.of_forall (fun b hb => hsub hb))
    _ ≤ 6 * C * F γ N * calE γ κ N ^ (-(2 / 3 : ℝ)) := HN₂ N hN₂ a ha

end LeanLab.ExceptionalSet.Decomp553b
