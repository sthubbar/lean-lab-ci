import LeanLab.ExceptionalSet.Decomp553d

/-!
Split of `Decomp553d.leaf_inner_high_j1`, the derived inner large phase mass
estimate on the assigned upper block `indices_high_j1` of the half interval.

The estimate is cut into the two inputs its argument actually needs.

  * The localization of large values of the restricted block phase: if the
    phase of the assigned upper block exceeds `N E ^ (-(5 / 6))`, then the
    shifted point `b - a` lies within `X ^ (δ - 1)` of a half integer.
  * The prime square supremum on the truncated minor arc, which turns a point of
    the truncated domain into a bound for the weighted prime mass.

Everything else is already in place: the finite strip cover, the strip volume,
the pointwise mass bound, the scalar absorption of the finite strip losses and
the eventual margins are combined in `UpJ200.Decomp539a.prime_strip_inner`,
which the assembly applies to the set where the assigned block phase is large.

Neither leaf mentions the mass weight together with the block phase, so each is
strictly weaker than the inner mass estimate. No existing file is edited, and the
assembly does not use the target theorem.
-/

namespace LeanLab.ExceptionalSet.Decomp553d

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF. Step 1, the localization of large values. For every admissible width
`δ` and every admissible cap for `κ` there is an eventual threshold such that at
every point `a` of the truncated minor window, every `b` of that window whose
assigned upper block phase exceeds the threshold `N E ^ (-(5 / 6))` lies within
`X ^ (δ - 1)` of a half integer. This is the localization step that the block
argument needs; it carries no integral and no mass, so it is strictly weaker
than the inner mass estimate. -/
theorem leaf_high_j1_large_phase_localizes (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                  ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ →
                ∃ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) := by
  classical
  obtain ⟨δp, hδp, hp⟩ := leaf_parity_gap γ h1 h2
  refine ⟨min δp 1, lt_min hδp one_pos, fun δ hδ hδs => ?_⟩
  have hδp' : δ < δp := hδs.trans_le (min_le_left _ _)
  obtain ⟨κp, hκp, hp⟩ := hp δ hδ hδp'
  refine ⟨κp, hκp, fun κ hκ hκs => ?_⟩
  obtain ⟨Np, hp⟩ := hp κ hκ hκs
  obtain ⟨Nw, hw⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδs.le hκ
  refine ⟨max Np Nw, fun N hN => ?_⟩
  have hNp : Np ≤ N := (le_max_left _ _).trans hN
  have hNw : Nw ≤ N := (le_max_right _ _).trans hN
  intro a ha b hb hlarge
  obtain ⟨-, hE1, -, hlog, hscale, hTX, -, hr, hXr⟩ := hw N hNw
  have hba : |b - a| ≤ F γ N ^ δ := by
    have hb1 : b ≤ calE γ κ N ^ (2 / 3 : ℝ) := hb.2.2
    have hb2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ b := hb.2.1
    have ha1 : a ≤ calE γ κ N ^ (2 / 3 : ℝ) := ha.2.2
    have ha2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ a := ha.2.1
    have hE0 : 0 < calE γ κ N := Real.exp_pos _
    have hEp : (0 : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) := Real.rpow_nonneg hE0.le _
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨h, hh⟩ := hp N hNp (b - a) hba hlarge
  exact ⟨h, hh⟩

/-- LEAF. Step 2, the prime square supremum on the truncated minor arc. There is
an admissible width `δ` and a constant such that, eventually, every point of the
truncated domain carries a prime square bounded by `C X ^ (2 - 6 δ) log X ^ 8`.
This is one estimate for a single prime sum: it says nothing about the block
phase, the doubled moment or the mass weight, so it is strictly weaker than the
inner mass estimate. -/
theorem leaf_high_j1_minor_prime_sup (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ b ∈ UpJ200.Decomp404e.truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
          ‖U1539.Sp (F γ N ^ (6 * δ)) (F γ N) b‖ ^ 2 ≤
            C * F γ N ^ (2 - 6 * δ) * Real.log (F γ N) ^ 8 := by
  exact UpJ200.MinorSup446.leaf_minor_sup_supplied γ h1 h2

/-- Assembly. The two steps above give the inner large phase mass estimate on the
assigned upper block. The set on which the block phase is large sits inside the
truncated minor window, and the localization puts it inside the finite union of
localized half integer strips: the index of the strip is bounded because both
endpoints of `b - a` lie in the truncated window and the strip radius is at most
one. The strip cover, the strip volume and the scalar absorption are then the
ready-made `prime_strip_inner`. -/
theorem leaf_inner_high_j1_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
              {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖},
              mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b) ≤
                6 * C * F γ N * calE γ κ N ^ (-(2 / 3 : ℝ)) := by
  classical
  obtain ⟨δl, hδl, hloc⟩ := leaf_high_j1_large_phase_localizes γ h1 h2
  obtain ⟨δm, hδm, hsup⟩ := leaf_high_j1_minor_prime_sup γ h1 h2
  refine ⟨min (min δl δm) 1, lt_min (lt_min hδl hδm) one_pos, fun δ hδ hδs => ?_⟩
  have hδl' : δ < δl := hδs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδm' : δ < δm := hδs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδs.le.trans (min_le_right _ _)
  obtain ⟨κ₀, hκ₀, hloc⟩ := hloc δ hδ hδl'
  obtain ⟨C, hC, Nm, hsup⟩ := hsup δ hδ hδm'
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨Nl, hloc⟩ := hloc κ hκ hκs
  obtain ⟨Np, hp⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδ1 hκ
  refine ⟨C, hC, max Nl (max Nm (max Np 1)), fun N hN => ?_⟩
  have hNl : Nl ≤ N := by omega
  have hNm : Nm ≤ N := by omega
  have hNp : Np ≤ N := by omega
  obtain ⟨-, hE1, -, hlog, hscale, hTX, -, hr, hXr⟩ := hp N hNp
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hΔ1 : calE γ κ N ^ (-(5 / 12 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hE1 (by norm_num)
  intro a ha
  have hSodd : (oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
      {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
        ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖}) ⊆
      oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) := Set.inter_subset_left
  have hSstrips : (oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
      {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
        ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖}) ⊆
      strips (calE γ κ N) (F γ N) δ a := by
    intro b hb
    obtain ⟨hbA, hblarge⟩ := hb
    obtain ⟨h, hh⟩ := hloc N hNl a ha b hbA hblarge
    have hba : |b - a| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) := by
      have hb1 : b ≤ calE γ κ N ^ (2 / 3 : ℝ) := hbA.2.2
      have hb2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ b := hbA.2.1
      have ha1 : a ≤ calE γ κ N ^ (2 / 3 : ℝ) := ha.2.2
      have ha2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ a := ha.2.1
      rw [abs_le]
      constructor <;> linarith
    have hhup : (b - a) - (h : ℝ) / 2 ≤ F γ N ^ (δ - 1) := (abs_le.mp hh).2
    have hhdn : -(F γ N ^ (δ - 1)) ≤ (b - a) - (h : ℝ) / 2 := (abs_le.mp hh).1
    have hble : b - a ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) := (abs_le.mp hba).2
    have hbge : -(2 * calE γ κ N ^ (2 / 3 : ℝ)) ≤ b - a := (abs_le.mp hba).1
    have hle : (h : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
      have hstep : (h : ℝ) / 2 ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) + F γ N ^ (δ - 1) := by
        linarith
      nlinarith [hstep, hr, hXr]
    have hge : ((-h : ℤ) : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
      push_cast
      have hstep : -((h : ℝ)) / 2 ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) + F γ N ^ (δ - 1) := by
        linarith
      nlinarith [hstep, hr, hXr]
    have hmem : h ∈ stripIndices (calE γ κ N) := by
      have hup : h ≤ ⌊calE γ κ N ^ (3 / 4 : ℝ)⌋ := Int.le_floor.mpr hle
      have hdn : -h ≤ ⌊calE γ κ N ^ (3 / 4 : ℝ)⌋ := Int.le_floor.mpr hge
      simp only [stripIndices, Finset.mem_Icc]
      omega
    have hIcc : b ∈ Set.Icc (a + (h : ℝ) / 2 - F γ N ^ (δ - 1))
        (a + (h : ℝ) / 2 + F γ N ^ (δ - 1)) := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    exact Set.mem_iUnion₂.mpr ⟨h, hmem, hIcc⟩
  exact prime_strip_inner (calE γ κ N) (F γ N) C δ hE1.le hX0 hC.le hΔ1 hTX hlog
    hscale (fun b hb => hsup N hNm b hb) a _ hSodd hSstrips

end LeanLab.ExceptionalSet.Decomp553d
