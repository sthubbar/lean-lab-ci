import LeanLab.LanguascoPerelli1996.Mass108
import LeanLab.LanguascoPerelli1996.Partial318

/-!
P0071 page 355 display 13, symmetric height partial summation.
Interpolate between the zeroth and second frequency moments.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp318a
open Complex Real MeasureTheory intervalIntegral Interpolation318

/-- Page 355 display 13, derived finite representation with every symmetric prefix.
The same finite index set represents all cutoffs between U and T. -/
theorem band_prefix_representation {X : ℝ} (hX : 0 < X) {U T : ℝ} (hUT : U ≤ T)
    (q : ℕ) [NeZero q] (a : ℕ) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ),
      (∀ i ∈ s, U < |γ i| ∧ |γ i| ≤ T) ∧
      (∀ v : ℝ, zSum (X * Real.exp v) U T q a =
        ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)) ∧
      ∀ u : ℝ, U ≤ u → u ≤ T → ∀ v : ℝ,
        zSum (X * Real.exp v) U u q a =
          ∑ i ∈ s, (if |γ i| ≤ u then c i else 0) * Complex.exp (Complex.I * γ i * v) := by
  classical
  let s : Finset (Σ _χ : DirichletCharacter ℂ q, ℂ) :=
    Finset.univ.sigma (fun χ =>
      ((Zeros108.ntZeros_finite χ T).sdiff (t := {ρ : ℂ | |ρ.im| ≤ U})).toFinset)
  let c : (Σ _χ : DirichletCharacter ℂ q, ℂ) → ℂ := fun i =>
    i.1 (a : ZMod q) * tau i.1⁻¹ * (mult i.1 i.2 : ℂ) *
      Complex.exp (Complex.I * (i.2.im : ℂ) * (Real.log X : ℂ))
  let γ : (Σ _χ : DirichletCharacter ℂ q, ℂ) → ℝ := fun i => i.2.im
  have hs : ∀ i ∈ s, U < |γ i| ∧ |γ i| ≤ T := by
    intro i hi
    simp only [s, Finset.mem_sigma, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
      Set.mem_sdiff, Set.mem_setOf_eq, ntZeros] at hi
    exact ⟨lt_of_not_ge hi.2, hi.1.2.2.2⟩
  have hp : ∀ u : ℝ, U ≤ u → u ≤ T → ∀ v : ℝ,
      zSum (X * Real.exp v) U u q a =
        ∑ i ∈ s, (if |γ i| ≤ u then c i else 0) * Complex.exp (Complex.I * γ i * v) := by
    intro u hUu huT v
    rw [Band108.zSum_eq_sum]
    simp only [s, c, γ, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro χ _
    have he : ((Zeros108.ntZeros_finite χ u).sdiff (t := {ρ : ℂ | |ρ.im| ≤ U})).toFinset =
        (((Zeros108.ntZeros_finite χ T).sdiff (t := {ρ : ℂ | |ρ.im| ≤ U})).toFinset).filter
          (fun ρ : ℂ => |ρ.im| ≤ u) := by
      ext ρ
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_sdiff,
        Set.mem_setOf_eq, ntZeros]
      constructor
      · rintro ⟨⟨h0, h1, h2, hu⟩, hnot⟩
        exact ⟨⟨⟨h0, h1, h2, hu.trans huT⟩, hnot⟩, hu⟩
      · rintro ⟨⟨⟨h0, h1, h2, _⟩, hnot⟩, hu⟩
        exact ⟨⟨h0, h1, h2, hu⟩, hnot⟩
    rw [he, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    split_ifs
    · rw [Real.log_mul hX.ne' (Real.exp_pos v).ne', Real.log_exp,
        Complex.ofReal_add, mul_add, Complex.exp_add]
      ring
    · simp
  refine ⟨_, s, c, γ, hs, ?_, hp⟩
  intro v
  rw [hp T hUT le_rfl v]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (hs i hi).2]

/-- LEAF. Page 355 display 13, the derived even moment partial summation step.
A nonnegative multiplier gamma squared uses only symmetric height prefixes.
This finite Abel estimate has no derivative, character or GRH input. -/
theorem even_moment_mass {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ)
    {U T M : ℝ} (hU : 0 ≤ U) (hUT : U < T) (hM : 0 ≤ M)
    (hγ : ∀ i ∈ s, U < |γ i| ∧ |γ i| ≤ T)
    (hmass : ∀ u : ℝ, U ≤ u → u ≤ T →
      mass s (fun i => if |γ i| ≤ u then c i else 0) γ ≤ M) :
    mass s (fun i => (γ i : ℂ) ^ 2 * c i) γ ≤ 4 * T ^ 4 * M := by
  classical
  by_cases hs : s = ∅
  · subst s
    simp only [mass, Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, integral_zero]
    positivity
  let H := s.image (fun i => |γ i|)
  have hH : H.Nonempty := (Finset.nonempty_iff_ne_empty.mpr hs).image _
  have hcardpos : 0 < H.card := Finset.card_pos.mpr hH
  let N := H.card - 1
  have hcard : H.card = N + 1 := by
    dsimp only [N]
    omega
  let e := H.orderIsoOfFin hcard
  let idx : (i : ι) → i ∈ s → Fin (N + 1) := fun i hi =>
    e.symm ⟨|γ i|, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  let f : ℕ → ι → ℂ := fun k i =>
    if hi : i ∈ s then if (idx i hi).val = k then c i else 0 else 0
  let w : ℕ → ℝ := fun k => (e ⟨min k N, by omega⟩ : ℝ) ^ 2
  have hheight (k : Fin (N + 1)) : U < (e k : ℝ) ∧ (e k : ℝ) ≤ T := by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (e k).property
    simpa only [← he] using hγ i hi
  have hw : Monotone w := by
    intro k l hkl
    apply pow_le_pow_left₀ (hU.trans (hheight _).1.le)
    exact e.monotone (show (⟨min k N, by omega⟩ : Fin (N + 1)) ≤ ⟨min l N, by omega⟩ from
      min_le_min_right N hkl)
  have hw0 : 0 ≤ w 0 := sq_nonneg _
  have hpre (k : ℕ) (hk : k ≤ N) (i : ι) (hi : i ∈ s) :
      (∑ j ∈ Finset.range (k + 1), f j i) =
        if |γ i| ≤ (e ⟨k, by omega⟩ : ℝ) then c i else 0 := by
    have hh : (idx i hi).val ≤ k ↔ |γ i| ≤ (e ⟨k, by omega⟩ : ℝ) := by
      have hh := (e.le_iff_le (x := idx i hi) (y := ⟨k, by omega⟩)).symm
      change (idx i hi).val ≤ k ↔ (e (idx i hi) : ℝ) ≤ (e ⟨k, by omega⟩ : ℝ) at hh
      simpa only [idx, OrderIso.apply_symm_apply] using hh
    simp only [f, dif_pos hi, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hh]
  have hp (k : ℕ) (hk : k ≤ N) :
      mass s (fun i => ∑ j ∈ Finset.range (k + 1), f j i) γ ≤ M := by
    rw [Partial318.mass_congr s _ _ γ (fun i hi => hpre k hk i hi)]
    exact hmass (e ⟨k, by omega⟩) (hheight _).1.le (hheight _).2
  have hcoef (i : ι) (hi : i ∈ s) :
      (∑ k ∈ Finset.range (N + 1), (w k : ℂ) * f k i) = (γ i : ℂ) ^ 2 * c i := by
    have hh : w (idx i hi).val = γ i ^ 2 := by
      have hfin : (⟨min (idx i hi).val N, by omega⟩ : Fin (N + 1)) = idx i hi := by
        apply Fin.ext
        exact Nat.min_eq_left (Nat.le_of_lt_succ (idx i hi).isLt)
      change (e (⟨min (idx i hi).val N, by omega⟩ : Fin (N + 1)) : ℝ) ^ 2 = γ i ^ 2
      rw [hfin]
      simp only [idx, OrderIso.apply_symm_apply, sq_abs]
    simp only [f, dif_pos hi, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
      (idx i hi).isLt, if_pos, hh, Complex.ofReal_pow]
  rw [← Partial318.mass_congr s _ _ γ hcoef]
  have hb := Partial318.monotone_mass_le s γ f w N hM hw0 hw hp
  have hwN : w N ≤ T ^ 2 := by
    dsimp only [w]
    exact pow_le_pow_left₀ (hU.trans (hheight _).1.le) (hheight _).2 2
  have hwN0 : 0 ≤ w N := sq_nonneg _
  have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwN0 hwN 2) hM
  nlinarith

/-- Page 355 display 13, derived local mass bound for a differentiated finite sum. -/
theorem local_derivative_mass_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    (∫ v in (-1 : ℝ)..1,
      ‖deriv (fun t : ℝ => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)) v‖ ^ 2) ≤
        Real.exp 2 * mass s (fun i => (γ i : ℂ) * c i) γ := by
  classical
  have hd (v : ℝ) : HasDerivAt
      (fun t : ℝ => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t))
      (Complex.I * ∑ i ∈ s, (γ i : ℂ) * c i * Complex.exp (Complex.I * γ i * v)) v := by
    have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) v := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
        Complex.ofRealCLM.hasDerivAt
    have hi (i : ι) : HasDerivAt (fun t : ℝ => c i * Complex.exp (Complex.I * γ i * t))
        (Complex.I * ((γ i : ℂ) * c i * Complex.exp (Complex.I * γ i * v))) v := by
      convert ((hcast.const_mul (Complex.I * γ i)).cexp.const_mul (c i)) using 1 <;> ring
    simpa only [Finset.mul_sum] using HasDerivAt.fun_sum (u := s) (fun i _ => hi i)
  have he (v : ℝ) :
      ‖deriv (fun t : ℝ => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)) v‖ ^ 2 =
        ‖∑ i ∈ s, (γ i : ℂ) * c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 := by
    rw [(hd v).deriv, norm_mul, Complex.norm_I, one_mul]
  simp_rw [he]
  exact Mass108.local_mass_le_weighted (by fun_prop) (fun _ => sq_nonneg _)
    (FiniteEnergy108.finite_energy_identity s (fun i => (γ i : ℂ) * c i) γ).1

/-- Page 355 display 13, exactly the sealed band_derivative_mass statement.
The finite even moment estimate supplies the partial summation step. -/
theorem band_derivative_mass_decomposed :
    GRH → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          (∫ v in (-1 : ℝ)..1,
            ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) ≤
              C * T ^ 2 * M := by
  intro _hGRH
  refine ⟨20 * Real.exp 2, by positivity, ?_⟩
  intro X hX U T hU hUT hT q inst a _ha M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM U le_rfl hUT.le)
  obtain ⟨ι, s, c, γ, hγ, hsum, hprefix⟩ := band_prefix_representation hX hUT.le q a
  have hmass (u : ℝ) (hUu : U ≤ u) (huT : u ≤ T) :
      mass s (fun i => if |γ i| ≤ u then c i else 0) γ ≤ 4 * M := by
    unfold mass
    simp_rw [← hprefix u hUu huT]
    have hloc (t : ℝ) := Mass108.full_weighted_mass hX t q a
    have hc (t : ℝ) := (Correlation108.correlation_identity hX t q a).1
    have hint : (∫ v : ℝ, ‖zSum (X * Real.exp v) U u q a‖ ^ 2 * Real.exp (-2 * |v|)) ≤
        2 * (‖F X u q a‖ + ‖F X U q a‖) := by
      have hi := (FiniteEnergy108.finite_energy_identity s
        (fun i => if |γ i| ≤ u then c i else 0) γ).1
      simp_rw [← hprefix u hUu huT] at hi
      have hr := ((hc u).add (hc U)).const_mul (2 : ℝ)
      have hh := integral_mono hi hr (fun v => by
        rw [Mass108.zSum_band_eq_sub _ _ _ hUu]
        have hn := pow_le_pow_left₀ (norm_nonneg _)
          (norm_sub_le (zSum (X * Real.exp v) (-1) u q a)
            (zSum (X * Real.exp v) (-1) U q a)) 2
        have hp : ‖zSum (X * Real.exp v) (-1) u q a - zSum (X * Real.exp v) (-1) U q a‖ ^ 2 ≤
            2 * (‖zSum (X * Real.exp v) (-1) u q a‖ ^ 2 +
              ‖zSum (X * Real.exp v) (-1) U q a‖ ^ 2) := by
          nlinarith [sq_nonneg (‖zSum (X * Real.exp v) (-1) u q a‖ -
            ‖zSum (X * Real.exp v) (-1) U q a‖)]
        convert mul_le_mul_of_nonneg_right hp (Real.exp_pos (-2 * |v|)).le using 1 <;> simp only [Pi.add_apply] <;> ring)
      simp only [Pi.add_apply] at hh
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add (hc u) (hc U), hloc u, hloc U] at hh
      exact hh
    nlinarith [hM u hUu huT, hM U le_rfl hUT.le]
  have hbase : mass s c γ ≤ 4 * M := by
    have hh := hmass T hUT.le le_rfl
    have he : mass s (fun i => if |γ i| ≤ T then c i else 0) γ = mass s c γ := by
      exact Partial318.mass_congr s _ _ γ (fun i hi => if_pos (hγ i hi).2)
    rwa [he] at hh
  have hsecond := even_moment_mass s c γ hU hUT (by positivity : 0 ≤ 4 * M) hγ hmass
  have hfirst := mass_first_le s c γ hT (by positivity : 0 ≤ 4 * M) hbase hsecond
  have hf : (fun t : ℝ => zSum (X * Real.exp t) U T q a) =
      (fun t : ℝ => ∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * t)) := funext hsum
  rw [hf]
  have hl := local_derivative_mass_le s c γ
  nlinarith [mul_le_mul_of_nonneg_left hfirst (Real.exp_pos 2).le]

end LeanLab.LanguascoPerelli1996.Decomp318a

#print axioms LeanLab.LanguascoPerelli1996.Decomp318a.band_prefix_representation
#print axioms LeanLab.LanguascoPerelli1996.Decomp318a.even_moment_mass

#print axioms LeanLab.LanguascoPerelli1996.Decomp318a.local_derivative_mass_le
#print axioms LeanLab.LanguascoPerelli1996.Decomp318a.band_derivative_mass_decomposed
