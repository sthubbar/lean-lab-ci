/-
FALSE under GRH. The leaf log_L_prime_power_series1622 of
Linnik1951/SPLIT_mellin_lnL_expansion1622 cannot hold together with GRH.

At N = 8 the line 1/2 + 1/ln 8 + i t has real part below 1, and the prime power double
series on its right side, written with the lab tsum, is not summable over the primes, by
the argument of FALSE_mellin_prime_power_series1622 with the nonprincipal character chi_4
modulo 4, of modulus 1 at every odd prime. So the right side is 0 and the leaf says that
log L of chi_4 is 0 on the whole line. Under GRH, L of chi_4 does not vanish there, so
L of chi_4 equals 1 on the line, hence everywhere by the identity theorem, since L of a
nonprincipal character is entire. But chi_4 is odd and its L-function vanishes at -1.
Hence GRH and the leaf together are contradictory: the leaf can be proved only by
refuting GRH, and it is false if GRH holds.

The paper's Euler product identity is true for the analytic logarithm with the prime sum
taken in the conditionally convergent sense; the defect is in the lab tsum.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.FALSE_mellin_prime_power_series1622
import LeanLab.Linnik1951.Supply471

namespace LeanLab.Linnik1951

open Filter Topology

/-- The character chi_4 has modulus 1 at every odd natural number. -/
theorem norm_chi4_odd1622F (n : ℕ) (hn : n % 2 = 1) :
    ‖(ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (n : ZMod 4)‖ = 1 := by
  rw [MulChar.ringHomComp_apply, ZMod.χ₄_nat_eq_if_mod_four]
  simp only [hn, one_ne_zero, ite_false]
  split_ifs <;> simp

/-- chi_4 is not the principal character modulo 4. -/
theorem chi4_ne_one1622F : (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 4) ≠ 1 := by
  intro h
  have h3 := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  have hu : IsUnit (3 : ZMod 4) := isUnit_iff_exists_inv.mpr ⟨3, by decide⟩
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply hu] at h3
  have : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [this] at h3
  norm_num at h3

/-- chi_4 is odd. -/
theorem chi4_odd1622F :
    DirichletCharacter.Odd (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 4) := by
  unfold DirichletCharacter.Odd
  rw [MulChar.ringHomComp_apply]
  have : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  rw [this]; simp

/-- On the line at N = 8 the prime power double series of chi_4 is not summable over the
primes, so its lab tsum is 0 at every height. -/
theorem not_summable_line_eight_chi4_1622F (t : ℝ) :
    ¬ Summable (fun p : Nat.Primes => ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 4)
          ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 8 t))) := by
  intro hS
  set χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) with hχdef
  set s := mellinLine1622 8 t with hs
  set σ := 1 / 2 + 1 / Real.log 8 with hσ
  have hre : s.re = σ := re_line_eight1622F t
  obtain ⟨hσ1, hσ2⟩ := sigma_eight_bounds1622F
  set c : ℝ := (2 : ℝ) ^ (-σ) with hc
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let a : Nat.Primes → ℕ → ℂ := fun p m =>
    ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) * (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)
  let x : Nat.Primes → ℝ := fun p => ((p : ℕ) : ℝ) ^ (-σ)
  have hx0 : ∀ p, 0 ≤ x p := fun p => by positivity
  have hxc : ∀ p, x p ≤ c := fun p =>
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le) (by linarith)
  have hnorm : ∀ p m, ‖a p m‖ =
      ((m : ℝ) + 1)⁻¹ * ‖χ ((p : ℕ) ^ (m + 1))‖ * x p ^ (m + 1) := by
    intro p m
    show ‖((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) * (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)‖ = _
    rw [norm_mul, norm_mul, norm_term1622F, hre, norm_inv]
    have : (m : ℂ) + 1 = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hle : ∀ p m, ‖a p m‖ ≤ x p ^ (m + 1) := by
    intro p m
    rw [hnorm]
    have h1 : ((m : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have h2 : ‖χ ((p : ℕ) ^ (m + 1))‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have h3 : 0 ≤ x p ^ (m + 1) := pow_nonneg (hx0 p) _
    calc ((m : ℝ) + 1)⁻¹ * ‖χ ((p : ℕ) ^ (m + 1))‖ * x p ^ (m + 1)
        ≤ 1 * 1 * x p ^ (m + 1) := by gcongr
      _ = _ := by ring
  have hgeo : ∀ p, Summable (fun m : ℕ => x p ^ (m + 1)) := fun p => by
    have h0 := (summable_geometric_of_lt_one (hx0 p) (lt_of_le_of_lt (hxc p) hc1)).mul_left (x p)
    have he : (fun m : ℕ => x p * x p ^ m) = fun m : ℕ => x p ^ (m + 1) := by
      funext m; ring
    rw [he] at h0; exact h0
  have hsa : ∀ p, Summable (a p) := fun p => Summable.of_norm_bounded (hgeo p) (hle p)
  let R : Nat.Primes → ℂ := fun p => ∑' m, a p (m + 1)
  have hR : ∀ p, ‖R p‖ ≤ (1 - c)⁻¹ * ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    intro p
    have hxp := hx0 p
    have hx1 : x p < 1 := lt_of_le_of_lt (hxc p) hc1
    have hsum2 : Summable (fun m : ℕ => x p ^ (m + 2)) := by
      have h0 := (summable_geometric_of_lt_one hxp hx1).mul_left (x p ^ 2)
      have he : (fun m : ℕ => x p ^ 2 * x p ^ m) = fun m : ℕ => x p ^ (m + 2) := by
        funext m; ring
      rw [he] at h0; exact h0
    have h1 : ‖R p‖ ≤ ∑' m : ℕ, x p ^ (m + 2) :=
      tsum_of_norm_bounded hsum2.hasSum (fun m => hle p (m + 1))
    have h2 : ∑' m : ℕ, x p ^ (m + 2) = x p ^ 2 * (1 - x p)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hxp hx1, ← tsum_mul_left]
      congr 1; funext m; ring
    have h3 : x p ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
      simp only [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; ring
    have h4 : (1 - x p)⁻¹ ≤ (1 - c)⁻¹ := by
      apply inv_anti₀ (by linarith) (by linarith [hxc p])
    rw [h2, h3] at h1
    calc ‖R p‖ ≤ _ := h1
      _ ≤ ((p : ℕ) : ℝ) ^ (-(2 * σ)) * (1 - c)⁻¹ := by gcongr
      _ = _ := mul_comm _ _
  have hRs : Summable R := by
    refine Summable.of_norm_bounded ?_ hR
    exact (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left _
  have hhead : Summable (fun p => a p 0) := by
    have : (fun p => a p 0) = fun p => (∑' m, a p m) - R p := by
      funext p
      rw [(hsa p).tsum_eq_zero_add]; ring
    rw [this]; exact hS.sub hRs
  -- the exceptional prime 2, where chi_4 vanishes
  let e : Nat.Primes → ℝ := fun p => if (p : ℕ) = 2 then 1 else 0
  have he : Summable e := by
    apply summable_of_ne_finset_zero (s := {⟨2, Nat.prime_two⟩})
    intro p hp
    have : (p : ℕ) ≠ 2 := fun h2 => hp (Finset.mem_singleton.mpr (Subtype.ext h2))
    show (if (p : ℕ) = 2 then (1 : ℝ) else 0) = 0
    rw [if_neg this]
  have hbound : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) ≤ ‖a p 0‖ + e p := by
    intro p
    rcases p.prop.eq_two_or_odd with h2 | hodd
    · have hx1 : x p ≤ 1 := le_trans (hxc p) hc1.le
      have : e p = 1 := by simp [e, h2]
      rw [this]
      have := norm_nonneg (a p 0)
      show x p ≤ _
      linarith
    · have hne : (p : ℕ) ≠ 2 := by omega
      have he0 : e p = 0 := by simp [e, hne]
      rw [he0, add_zero, hnorm]
      have hchi : ‖χ ((p : ℕ) ^ (0 + 1))‖ = 1 := by
        have := norm_chi4_odd1622F (p : ℕ) hodd
        rw [zero_add, pow_one]; exact this
      rw [hchi]; simp [x]
  have hn : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le (fun p => by positivity) hbound (hhead.norm.add he)
  have := Nat.Primes.summable_rpow.mp hn
  linarith

/-- Under GRH the leaf log_L_prime_power_series1622, verbatim, is false: at N = 8 and chi_4
it would make L of chi_4 equal to 1 on the line, hence everywhere, against the zero of
L of chi_4 at -1. -/
theorem not_log_L_prime_power_series1622 (hG : LeanLab.DERZ1997.GRH) :
    ¬ (∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ t : ℝ, Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))
        = ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 N t))) := by
  intro h
  set χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) with hχdef
  have hχ : χ ≠ 1 := chi4_ne_one1622F
  have hL1 : ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 8 t) = 1 := by
    intro t
    have hlog := (h 8 (by norm_num) 4 χ hχ t).trans
      (tsum_eq_zero_of_not_summable (not_summable_line_eight_chi4_1622F t))
    have hne := LFunction_ne_zero_right471 hG 4 χ hχ (mellinLine1622 8 t)
      (mellinLine_re_gt_half471 8 (by norm_num) t)
    rw [← Complex.exp_log hne, hlog, Complex.exp_zero]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ :=
    fun z _ => analyticAt_const
  have hcont : Continuous (mellinLine1622 8) := by
    unfold mellinLine1622; fun_prop
  have htend : Tendsto (fun n : ℕ => mellinLine1622 8 (1 / ((n : ℝ) + 1))) atTop
      (𝓝[≠] (mellinLine1622 8 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(hcont.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    refine Eventually.of_forall (fun n => ?_)
    intro hmem
    have him := congrArg Complex.im hmem
    simp [mellinLine1622] at him
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rcases him with h0 | h0 <;> (norm_cast at h0)
  have hfreq : ∃ᶠ z in 𝓝[≠] (mellinLine1622 8 0),
      DirichletCharacter.LFunction χ z = (fun _ : ℂ => (1 : ℂ)) z :=
    htend.frequently (Frequently.of_forall (fun n => hL1 _))
  have hall := AnalyticOnNhd.eq_of_frequently_eq han hconst hfreq
  have hzero := DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one chi4_odd1622F 0
  have h1 := congrFun hall (-(2 * ((0 : ℕ) : ℂ)) - 1)
  rw [hzero] at h1
  exact zero_ne_one h1

end LeanLab.Linnik1951
