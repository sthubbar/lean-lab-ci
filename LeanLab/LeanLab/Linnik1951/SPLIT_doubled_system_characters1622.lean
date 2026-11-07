/-
Unit U-1622. Split of the doubled system mass of the exceptional file of this folder.
The target statement stays exactly as it is; this file adds three leaves and one
assembly.

The argument, from pages 155, 160 and 166 of the scan. The square integral of the
doubled prime system over the arc system clipped to the unit interval is first rewritten
as an integral over the radius interval of the sum of the shifted squares at the reduced
residues: the system is the finitely many doubled rational intervals of denominator q,
so a nonnegative continuous function integrates over it at most as its shifted sum.
The shifted sum is then bounded pointwise, for every z, by the finite unit character
calculation: orthogonality of the unit group turns the sum over the reduced residues
into the principal square plus q times the nonprincipal squares, divided by the totient,
and the Gauss squares are at most q. Integrating that pointwise bound over the radius
interval and doubling the constant absorbs the factor two from the doubled error
interval.

No analytic input is invented here: the pointwise character calculation and the two
geometry steps are leaves, and the assembly only integrates the pointwise bound and adds
the doubled error size.
-/
import LeanLab.Linnik1951.SPLIT1622_exceptional

namespace LeanLab.Linnik1951

open MeasureTheory Filter Finset

/-- The reduced residues below q number the totient of q, in the form the assembly
uses for the counting of the doubled intervals. -/
private theorem card_reduced1622 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))

/-- LEAF. The covering step of the geometry. For q at least two and tau at least four,
every point of the arc system of denominator q that lies in the unit interval lies in
one of the doubled rational intervals of radius two over q tau about a reduced residue
below q. Only rational arithmetic and the positivity of q and tau are used; no
integration, no character and no bound on the prime system occurs. -/
theorem rational_cover1622 (q : ℕ) [NeZero q] (τ : ℝ) (hq : 2 ≤ q) (hτ : 4 ≤ τ) :
    arcSystem111 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
  rintro x ⟨⟨r, hrden, hrδ⟩, hx0, hx1⟩
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hRle : 2 / ((q : ℝ) * τ) ≤ 1 / (2 * (q : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [abs_le] at hrδ
  obtain ⟨hrlo, hrhi⟩ := hrδ
  have hrcq : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def, hrden]
  have hcop : r.num.natAbs.Coprime q := by
    have h := r.reduced
    rwa [hrden] at h
  have hnum_nonneg : 0 ≤ r.num := by
    by_contra hneg
    push_neg at hneg
    have hle : (r.num : ℝ) ≤ -1 := by
      have : r.num ≤ -1 := by omega
      exact_mod_cast this
    have hrle : (r : ℝ) ≤ -1 / (q : ℝ) := by
      rw [hrcq, div_le_div_iff₀ hqpos hqpos]
      nlinarith
    have hxle : x ≤ -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) := by linarith
    have hneg' : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) < 0 := by
      have hsplit : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) = -(1 / (2 * (q : ℝ))) := by
        field_simp
        ring
      rw [hsplit]
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  have hnum_lt : r.num < (q : ℤ) := by
    by_contra hge
    push_neg at hge
    have hne : r.num ≠ (q : ℤ) := by
      intro he
      have hnat : r.num.natAbs = q := by
        rw [he]
        exact Int.natAbs_natCast q
      rw [hnat] at hcop
      have hq1 : q = 1 := Nat.coprime_self q |>.mp hcop
      omega
    have hge' : (q : ℤ) + 1 ≤ r.num := by omega
    have hcastZ : ((q : ℤ) : ℝ) + 1 ≤ (r.num : ℝ) := by exact_mod_cast hge'
    have hcast : (q : ℝ) + 1 ≤ (r.num : ℝ) := by
      have hqZ : ((q : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
      linarith
    have hrbig : 1 + 1 / (q : ℝ) ≤ (r : ℝ) := by
      rw [hrcq, le_div_iff₀ hqpos]
      have hmul : (1 + 1 / (q : ℝ)) * (q : ℝ) = (q : ℝ) + 1 := by
        field_simp
      rw [hmul]
      exact hcast
    have hxge : 1 + 1 / (2 * (q : ℝ)) ≤ x := by
      have hsplit : (1 : ℝ) + 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 + 1 / (2 * (q : ℝ)) := by
        field_simp
        ring
      linarith
    have : (1 : ℝ) < 1 + 1 / (2 * (q : ℝ)) := by
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  set a := r.num.toNat with hadef
  have hanum : (a : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
  have halt : a < q := by
    have h' : (a : ℤ) < (q : ℤ) := by rw [hanum]; exact hnum_lt
    exact_mod_cast h'
  have hcopa : Nat.Coprime a q := by
    have hna : r.num.natAbs = a := by
      rw [hadef]
      have h1 : ((r.num.natAbs : ℕ) : ℤ) = r.num := Int.natAbs_of_nonneg hnum_nonneg
      have h2 : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
      exact_mod_cast h1.trans h2.symm
    rwa [hna] at hcop
  have hcasta : (a : ℝ) = (r.num : ℝ) := by
    have : (a : ℝ) = ((a : ℤ) : ℝ) := by push_cast; ring
    rw [this, hanum]
  have hmem : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨halt, hcopa⟩
  have hxI : x ∈ Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ))
      ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
    have e1 : (a : ℝ) / q - 2 / ((q : ℝ) * τ) = (r : ℝ) - 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    have e2 : (a : ℝ) / q + 2 / ((q : ℝ) * τ) = (r : ℝ) + 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    rw [Set.mem_Icc, e1, e2]
    constructor <;> linarith
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨a, hmem, hxI⟩


/-- LEAF. The integral step of the geometry. For a nonnegative continuous function and a
cover of the clipped arc system by the doubled intervals of the reduced residues, the
integral over the clipped system is at most the integral over the radius interval of the
sum of the shifted values at the reduced residues. This is subadditivity of the integral
over a finite union together with translation of the interval, so it uses no property of
the function beyond nonnegativity and continuity, and none of the characters. -/
theorem rational_cover_integral1622 (q : ℕ) [NeZero q] (τ : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hn : ∀ x : ℝ, 0 ≤ f x)
    (hcover : arcSystem111 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ))) :
    (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, f α) ≤
      ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f ((a : ℝ) / q + z) := by
  sorry

/-- LEAF. The finite unit character step, pointwise in z. At any z the sum of the squares
of the prime system shifted to the reduced residues below q is at most a constant over the
totient of q times the principal square plus q times the sum of the nonprincipal squares,
plus a constant times the totient of q times the square of the logarithm of q. The
orthogonality of the unit group gives the coefficient one over the totient, the Gauss
squares are bounded by q, and the primes dividing q are absorbed in the logarithmic term.
No tau, no integration and no growth hypothesis occurs. -/
theorem rational_pointwise_characters1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2 := by
  sorry

/-- The doubled system mass, from the two geometry steps and the pointwise finite
character bound. The target statement is unchanged. -/
theorem doubled_system_characters1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (2 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
  classical
  obtain ⟨B, hB, hb⟩ := rational_pointwise_characters1622
  refine ⟨2 * B, by positivity, ?_⟩
  intro N q _ τ hN hq hτ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτp : 0 < τ := by linarith
  set r := 2 / ((q : ℝ) * τ) with hrdef
  have hr : 0 < r := by positivity
  let F : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun χ => χ ≠ 1)
  let J : ℝ → ℝ := fun z => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
    (q : ℝ) * ∑ χ ∈ F, ‖characterPrime280 χ N z‖ ^ 2
  have hp : Continuous (fun z : ℝ => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) :=
    (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  have hc (χ : DirichletCharacter ℂ q) :
      Continuous (fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2) :=
    (continuous_character_prime357 χ N hN).norm.pow 2
  have hJ : Continuous J := hp.add ((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _)
  have hJ0 : ∀ z, 0 ≤ J z := by intro z; dsimp [J]; positivity
  have hS : Continuous (fun z => ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) :=
    continuous_finset_sum _ (fun a _ =>
      ((continuous_prime_fourier111 N hN).norm.pow 2).comp (continuous_const.add continuous_id))
  have hgeo := rational_cover_integral1622 q τ (fun α => ‖primeFourier111 N α‖ ^ 2)
    ((continuous_prime_fourier111 N hN).norm.pow 2) (fun α => sq_nonneg _)
    (rational_cover1622 q τ hq hτ)
  have hmono : (∫ z in -r..r, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      ∫ z in -r..r, B / (q.totient : ℝ) * J z + B * (q.totient : ℝ) * Real.log q ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) (hS.intervalIntegrable _ _)
      (((hJ.const_mul _).add continuous_const).intervalIntegrable _ _)
      (fun z _ => hb N q hN hq z)
  have hsplit : (∫ z in -r..r, J z) =
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        (q : ℝ) * ∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime280 χ N z‖ ^ 2 := by
    dsimp [J]
    rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      (((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finset_sum (fun χ _ => (hc χ).intervalIntegrable _ _)]
  have hpos : 0 ≤ B / (q.totient : ℝ) * (∫ z in -r..r, J z) :=
    mul_nonneg (div_nonneg hB.le (Nat.cast_nonneg _))
      (intervalIntegral.integral_nonneg_of_forall (by linarith) hJ0)
  rw [intervalIntegral.integral_add ((hJ.const_mul _).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal : B / (q.totient : ℝ) * (∫ z in -r..r, J z) +
      (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) ≤
      (2 * B) / (q.totient : ℝ) * (∫ z in -r..r, J z) +
        (2 * B) * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    calc
      _ ≤ 2 * (B / (q.totient : ℝ) * (∫ z in -r..r, J z)) +
          (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) := by linarith
      _ = _ := by ring
  have hh := hgeo.trans (hmono.trans hfinal)
  rw [hsplit] at hh
  exact hh

end LeanLab.Linnik1951
