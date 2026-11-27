import LeanLab.HelfgottMajor.SPLIT_tail_mass_integral

/-!
A conditional Lean refutation of the LEAF `exp_count_le_integral` of `SPLIT_tail_mass_integral`,
the exponential sibling of `gaussian_count_le_integral` in the tail mass step of P0014,
displays 4.35 and 4.36.

The leaf asks that the series of `exp (-0.1598 |Im ρ|)` over the strip zeros above height `T`
be summable with total at most `expTailIntegral q T`.  Burst burst-20261122, session S97,
reported it FALSE with Arb certified numerics at `q = 1`: the sum runs over both signs of the
ordinate while `countDensity` is the one sided density of display 4.35.

This file makes that a kernel checked implication at `q = 1`, `T = 101.3`.  Its one input,
`hzero`, is three zeros of `ζ` on the critical line with ordinates in `(101.3, 101.4]`,
`(103.7, 103.8]` and `(105.4, 105.5]`; these are `101.3178510057`, `103.7255380405` and
`105.4466230523`, the 30th to 32nd zeros with positive ordinate in the tables of Odlyzko and of
the LMFDB.  The upper side is the proved bound `Decomp269c.exp_integral_bound`, display 4.36:
the integral is at most `1.0242 · log (T/2π) · exp (-0.1598 T) < 3.08 exp (-0.1598 T)`, while
the three zeros and their conjugates give more than `3.8 exp (-0.1598 T)`.

CONDITIONAL ON that one input.  The leaf stays open in its file; no statement is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c.RefuteExpCount
open Real

/-- `log (101.3 / 2π) < 3`. -/
theorem log_top_lt_three : log (((1 : ℕ) : ℝ) * 101.3 / (2 * π)) < 3 := by
  have hpi1 := Real.pi_gt_d2
  have hπ : 0 < π := Real.pi_pos
  rw [Nat.cast_one, one_mul]
  have hx : 0 < 101.3 / (2 * π) := by positivity
  rw [Real.log_lt_iff_lt_exp hx]
  have he : (2.7 : ℝ) ^ 3 < exp 3 := by
    have h := Real.exp_one_gt_d9
    have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    exact pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
  have hq : 101.3 / (2 * π) < 16.2 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  nlinarith

/-- `exp (-0.1598 γ) ≥ (1 - 0.1598 (γ - T)) exp (-0.1598 T)`. -/
theorem exp_shift_ge (γ T : ℝ) :
    (1 - 0.1598 * (γ - T)) * exp (-0.1598 * T) ≤ exp (-0.1598 * γ) := by
  have h := Real.add_one_le_exp (-(0.1598 * (γ - T)))
  have hsplit : exp (-0.1598 * γ) = exp (-0.1598 * T) * exp (-(0.1598 * (γ - T))) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have h0 : 0 < exp (-0.1598 * T) := Real.exp_pos _
  nlinarith

/-- Conditional refutation of `exp_count_le_integral`.  CONDITIONAL ON three zeros of `ζ` on
the critical line with ordinates in `(101.3, 101.4]`, `(103.7, 103.8]`, `(105.4, 105.5]`. -/
theorem not_exp_count_le_integral (γ₁ γ₂ γ₃ : ℝ)
    (h1 : 101.3 < γ₁) (h1' : γ₁ ≤ 101.4) (h2 : 103.7 < γ₂) (h2' : γ₂ ≤ 103.8)
    (h3 : 105.4 < γ₃) (h3' : γ₃ ≤ 105.5)
    (hzero : ∀ γ ∈ ({γ₁, γ₂, γ₃} : Set ℝ),
      riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) (hT : 100 ≤ T),
        Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|)) ∧
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
          expTailIntegral q T) := by
  intro hleaf
  set χ : DirichletCharacter ℂ 1 := 1 with hχdef
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hT : (100 : ℝ) ≤ 101.3 := by norm_num
  obtain ⟨hs, hle⟩ := hleaf 1 χ 101.3 hT
  have hbound := exp_integral_bound 1 101.3 hT
  have hlog := log_top_lt_three
  let g : Fin 3 → ℝ := ![γ₁, γ₂, γ₃]
  have hgmono : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i
    fin_cases i <;> simp [g] <;> linarith
  have hgpos : ∀ k, 101.3 < g k := by
    intro k; fin_cases k <;> simp [g] <;> linarith
  have hgz : ∀ k, riemannZeta ((1 / 2 : ℂ) + (g k : ℂ) * Complex.I) = 0 := by
    intro k; fin_cases k <;> simp only [g] <;> apply hzero <;> simp
  let f : Fin 3 × Bool → ℂ := fun p =>
    (1 / 2 : ℂ) + ((if p.2 then g p.1 else -g p.1 : ℝ) : ℂ) * Complex.I
  have him : ∀ p, (f p).im = (if p.2 then g p.1 else -g p.1) := by
    intro p; simp [f]
  have hre : ∀ p, (f p).re = 1 / 2 := by
    intro p; simp [f]
  have habsim : ∀ p, |(f p).im| = g p.1 := by
    intro p
    have hp := hgpos p.1
    rw [him]; split_ifs
    · exact abs_of_pos (by linarith)
    · rw [abs_neg]; exact abs_of_pos (by linarith)
  have hfz : ∀ p, riemannZeta (f p) = 0 := by
    rintro ⟨k, b⟩
    cases b
    · have hc : f (k, false) = (starRingEnd ℂ) ((1 / 2 : ℂ) + (g k : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp [f]
      rw [hc, riemannZeta_conj, hgz k, map_zero]
    · have hc : f (k, true) = (1 / 2 : ℂ) + (g k : ℂ) * Complex.I := by
        simp [f]
      rw [hc, hgz k]
  have hmem : ∀ p, DirichletCharacter.LFunction χ (f p) = 0 ∧ 0 < (f p).re ∧ (f p).re < 1 ∧
      (101.3 : ℝ) < |(f p).im| := by
    intro p
    refine ⟨by rw [hL]; exact hfz p, by rw [hre]; norm_num, by rw [hre]; norm_num, ?_⟩
    rw [habsim]; exact hgpos p.1
  let F : Fin 3 × Bool → {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ (101.3 : ℝ) < |ρ.im|} := fun p => ⟨f p, hmem p⟩
  have hFinj : Function.Injective F := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hab
    have h := congrArg (fun x => x.val.im) hab
    simp only [F] at h
    rw [him, him] at h
    have ha := hgpos a
    have hc := hgpos c
    cases b <;> cases d <;> simp at h
    · exact Prod.ext (hgmono.injective h) rfl
    · linarith
    · linarith
    · exact Prod.ext (hgmono.injective h) rfl
  have hsle := hs.sum_le_tsum (Finset.univ.map ⟨F, hFinj⟩) (fun ρ _ => (Real.exp_pos _).le)
  rw [Finset.sum_map] at hsle
  simp only [Function.Embedding.coeFn_mk, F, habsim] at hsle
  rw [Fintype.sum_prod_type] at hsle
  simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Finset.sum_singleton, Fin.sum_univ_three] at hsle
  simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hsle
  have e1 := exp_shift_ge γ₁ 101.3
  have e2 := exp_shift_ge γ₂ 101.3
  have e3 := exp_shift_ge γ₃ 101.3
  have hE : 0 < exp (-0.1598 * (101.3 : ℝ)) := Real.exp_pos _
  have hub : 1.0242 * log (((1 : ℕ) : ℝ) * 101.3 / (2 * π)) * exp (-0.1598 * (101.3 : ℝ)) ≤
      1.0242 * 3 * exp (-0.1598 * (101.3 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hlog.le (by norm_num : (0 : ℝ) ≤ 1.0242)
    exact mul_le_mul_of_nonneg_right this hE.le
  have hc1 : (1 - 0.1598 * (γ₁ - 101.3)) ≥ 0.98 := by nlinarith
  have hc2 : (1 - 0.1598 * (γ₂ - 101.3)) ≥ 0.6 := by nlinarith
  have hc3 : (1 - 0.1598 * (γ₃ - 101.3)) ≥ 0.32 := by nlinarith
  have hcast : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  have p1 := mul_le_mul_of_nonneg_right hc1 hE.le
  have p2 := mul_le_mul_of_nonneg_right hc2 hE.le
  have p3 := mul_le_mul_of_nonneg_right hc3 hE.le
  rw [Finset.sum_pair (by decide), Finset.sum_pair (by decide),
    Finset.sum_pair (by decide)] at hsle
  push_cast at hbound hub hle
  linarith

end LeanLab.HelfgottMajor.Decomp269c.RefuteExpCount

#print axioms LeanLab.HelfgottMajor.Decomp269c.RefuteExpCount.not_exp_count_le_integral
