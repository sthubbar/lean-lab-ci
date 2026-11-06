import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.Applications
import LeanLab.Pintz2021.DecompJ281
import LeanLab.Pintz2021.DecompJ665
import LeanLab.RieselVaughan1983.GaussImprim

open Filter Topology Real Complex
open scoped Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53
open LeanLab.Pintz2021.DecompJ281
open LeanLab.Pintz2021.DecompJ665

namespace LeanLab.Pintz2021.DecompJ834

open Finset LeanLab.PNTPort.LargeSieve

/-! ### Helper lemmas for `leaf_singular_series_converges_3`

All new in this session: the Möbius decomposition of the coefficient sum, the bound
`‖τ_q(ind χ)‖² = conductor` at every level, the twisted Ramanujan bound `‖c_ψ(m)‖ ≤ √r σ(m)`, and
the `q^{-3/2}(1+log q)^2` majorant.  No statement of the file is changed. -/

noncomputable section



open LeanLab.PNTPort.LargeSieve in
/-- The lab's exponential is periodic in the integer direction. -/
theorem e_add_int (x : ℝ) (k : ℤ) : e (x + (k : ℝ)) = e x := by
  rw [e_add, e_int, mul_one]

open LeanLab.PNTPort.LargeSieve in
/-- Mathlib's standard additive character on `ZMod q` is the lab's exponential at `x.val/q`. -/
theorem stdAddChar_eq_e {q : ℕ} [NeZero q] (x : ZMod q) :
    ZMod.stdAddChar x = e ((x.val : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  unfold e
  congr 1
  push_cast
  ring

open LeanLab.PNTPort.LargeSieve in
/-- The standard additive character at a product of residues is the lab's exponential at the
corresponding real frequency. -/
theorem stdAddChar_mul_eq_e {q : ℕ} [NeZero q] (h : ℕ) (m : ℤ) :
    ZMod.stdAddChar ((h : ZMod q) * (m : ZMod q)) = e ((h : ℝ) * m / q) := by
  rw [stdAddChar_eq_e]
  have hcast : ((((h : ZMod q) * (m : ZMod q)).val : ℤ) : ZMod q) = ((h * m : ℤ) : ZMod q) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    push_cast
    ring
  have hdvd : (q : ℤ) ∣ (h * m) - ((((h : ZMod q) * (m : ZMod q)).val : ℤ)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp hcast
  obtain ⟨k, hk⟩ := hdvd
  have hkR : (h : ℝ) * m - ((((h : ZMod q) * (m : ZMod q)).val : ℤ) : ℝ) = (k : ℝ) * q := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at h ⊢
    linarith
  have hval : ((((h : ZMod q) * (m : ZMod q)).val : ℝ)) = (h : ℝ) * m - (k : ℝ) * q := by
    have h := hkR
    push_cast at h ⊢
    linarith
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have harg : ((((h : ZMod q) * (m : ZMod q)).val : ℝ) / q) =
      (h : ℝ) * m / q + ((-k : ℤ) : ℝ) := by
    rw [hval]
    push_cast
    field_simp
    ring
  rw [harg, e_add_int]


/-- Summing over the residues `0, …, n-1` is summing over `ZMod n`. -/
theorem sum_range_eq_sum_ZMod {n : ℕ} [NeZero n] (f : ZMod n → ℂ) :
    ∑ j ∈ Finset.range n, f (j : ZMod n) = ∑ a : ZMod n, f a := by
  refine Finset.sum_bij (fun j (_ : j ∈ Finset.range n) => (j : ZMod n)) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a₁ h₁ a₂ h₂ he
    simp only [Finset.mem_range] at h₁ h₂
    have h3 : a₁ ≡ a₂ [MOD n] := (ZMod.natCast_eq_natCast_iff a₁ a₂ n).mp he
    exact h3.eq_of_lt_of_lt h₁ h₂
  · intro b _
    exact ⟨b.val, Finset.mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
  · intro a _; rfl

/-- **Rotation of a primitive Gauss sum against an arbitrary frequency**: the twisted sum of a
primitive character has the size of the Gauss sum, `√r`, for every frequency. -/
theorem norm_sum_chi_mul_e_le {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (n : ℤ) :
    ‖∑ j ∈ Finset.range r, χ (j : ZMod r) * e ((j : ℝ) * (n : ℝ) / (r : ℝ))‖ ≤ Real.sqrt r := by
  have hsum : (∑ j ∈ Finset.range r, χ (j : ZMod r) * e ((j : ℝ) * (n : ℝ) / (r : ℝ)))
      = ∑ a : ZMod r, χ a * ZMod.stdAddChar (a * (n : ZMod r)) := by
    rw [← sum_range_eq_sum_ZMod (n := r)
      (fun a : ZMod r => χ a * ZMod.stdAddChar (a * (n : ZMod r)))]
    exact Finset.sum_congr rfl fun (j : ℕ) _ => by
      rw [← stdAddChar_mul_eq_e (q := r) j n]
  rw [hsum, ← LeanLab.RieselVaughan1983.GaussImprim.inv_mul_gaussSum_eq hχ (n : ZMod r)]
  refine le_trans (norm_mul_le _ _) ?_
  have h1 : ‖χ⁻¹ (n : ZMod r)‖ ≤ 1 := by
    by_cases hu : IsUnit (n : ZMod r)
    · have := χ⁻¹.unit_norm_eq_one hu.unit
      rw [hu.unit_spec] at this
      rw [this]
    · rw [MulChar.map_nonunit _ hu, norm_zero]
      exact zero_le_one
  have h2 : ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ)‖ = Real.sqrt r := by
    have := LeanLab.RieselVaughan1983.GaussImprim.norm_sq_gaussSum_of_isPrimitive hχ
    have hnn : (0 : ℝ) ≤ ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ)‖ := norm_nonneg _
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), Real.sqrt_nonneg (r : ℝ)]
  rw [h2]
  calc ‖χ⁻¹ (n : ZMod r)‖ * Real.sqrt r ≤ 1 * Real.sqrt r := by
        exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    _ = Real.sqrt r := one_mul _


/-! ### Rectangle reindexing of `range` sums -/

theorem sum_range_mul_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n : ℕ} (hn : 0 < n)
    (m : ℕ) :
    ∑ a ∈ Finset.range (n * m), f a = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f (j + n * i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
      exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm])

/-- `e θ = 1` forces `θ` to be an integer. -/
theorem exists_int_of_e_eq_one {x : ℝ} (h : e x = 1) : ∃ n : ℤ, x = n := by
  have h' : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) = 1 := h
  rw [Complex.exp_eq_one_iff] at h'
  obtain ⟨n, hn⟩ := h'
  have him : 2 * Real.pi * x = (n : ℝ) * (2 * Real.pi) := by
    have h1 := congrArg Complex.im hn
    simpa using h1
  refine ⟨n, ?_⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2 : x * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by linarith
  have := mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h2
  rw [this]

/-- The geometric sum vanishes away from the divisibility points. -/
theorem sum_range_e_div_eq_zero {s : ℕ} (hs : 0 < s) {m : ℤ} (hm : ¬ (s : ℤ) ∣ m) :
    ∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = 0 := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  set θ : ℝ := (m : ℝ) / (s : ℝ) with hθ
  have hterm : ∀ v : ℕ, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = e θ ^ v := by
    intro v
    have hv : (v : ℝ) * (m : ℝ) / (s : ℝ) = (v : ℝ) * θ := by
      simp only [hθ]; field_simp
    rw [hv, e_nat_mul]
  simp_rw [hterm]
  have hpow : e θ ^ s = 1 := by
    rw [← e_nat_mul]
    have h1 : (s : ℝ) * θ = (m : ℝ) := by
      simp only [hθ]; field_simp
    rw [h1, e_int]
  have hne : e θ ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := exists_int_of_e_eq_one h1
    exact hm ⟨k, by
      have : (m : ℝ) = ((s : ℤ) * k : ℤ) := by
        have h2 : (m : ℝ) = (s : ℝ) * θ := by simp only [hθ]; field_simp
        rw [h2, hk]; push_cast; ring
      exact_mod_cast this⟩
  rw [geom_sum_eq hne s, hpow, sub_self, zero_div]

/-- The geometric sum at a divisibility point is the whole length. -/
theorem sum_range_e_div_eq_card {s : ℕ} (hs : 0 < s) {m : ℤ} (hm : (s : ℤ) ∣ m) :
    ∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = (s : ℂ) := by
  obtain ⟨k, hk⟩ := hm
  have hterm : ∀ v : ℕ, e ((v : ℝ) * (m : ℝ) / (s : ℝ)) = 1 := by
    intro v
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have : (v : ℝ) * (m : ℝ) / (s : ℝ) = (v : ℝ) * (k : ℝ) := by
      rw [hk]; push_cast; field_simp
    rw [this]
    have h2 : (v : ℝ) * (k : ℝ) = (((v : ℤ) * k : ℤ) : ℝ) := by push_cast; ring
    rw [h2]
    exact e_int _
  simp_rw [hterm]
  simp

/-- The inner sum factors into the character sums over the residues mod `r` and the geometric
sum over the multiples of `r`. -/
theorem sum_range_chi_mul_e_factor {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (χ : DirichletCharacter ℂ r) (m : ℤ) :
    ∑ a ∈ Finset.range (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = (∑ j ∈ Finset.range r, χ (j : ZMod r) * e ((j : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
        * (∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ))) := by
  rw [sum_range_mul_range (f := fun a : ℕ =>
    χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))) (n := r) hr s,
    Finset.sum_comm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hchi : ((j + r * i : ℕ) : ZMod r) = (j : ZMod r) := by
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero]
  have he : ((j + r * i : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)
      = (j : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ) + (i : ℝ) * (m : ℝ) / (s : ℝ) := by
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  simp only [hchi, he, e_add, mul_assoc]

/-- **The inner sum at a general level**: it is bounded by `√r` times the length, and it vanishes
unless the level ratio divides the frequency. -/
theorem norm_sum_range_chi_mul_e_le {r s : ℕ} [NeZero r] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖∑ a ∈ Finset.range (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  have hr : 0 < r := NeZero.pos r
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [sum_range_chi_mul_e_factor hr hs χ m, norm_mul]
  by_cases hd : (s : ℤ) ∣ m
  · rw [ite_eq_left hd]
    obtain ⟨k, hk⟩ := hd
    have harg : ∀ j : ℕ, (j : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)
        = (j : ℝ) * (k : ℝ) / (r : ℝ) := by
      intro j
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      have hm : (m : ℝ) = (s : ℝ) * (k : ℝ) := by
        rw [hk]; push_cast; ring
      rw [hm]
      push_cast
      field_simp
    simp_rw [harg]
    have h2 := norm_sum_chi_mul_e_le hχ k
    have h3 : (∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ))) = (s : ℂ) :=
      sum_range_e_div_eq_card hs ⟨k, hk⟩
    rw [h3, Complex.norm_natCast]
    exact mul_le_mul h2 le_rfl (by positivity) (Real.sqrt_nonneg _)
  · rw [ite_eq_right hd]
    have h0 : (∑ v ∈ Finset.range s, e ((v : ℝ) * (m : ℝ) / (s : ℝ))) = 0 :=
      sum_range_e_div_eq_zero hs hd
    rw [h0, norm_zero, mul_zero]
    simp


/-! ### Möbius bookkeeping -/

open scoped ArithmeticFunction.Moebius in
/-- `∑_{d | n} μ(d) = [n = 1]`. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply
    (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ)) (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h, ArithmeticFunction.one_apply]

open scoped ArithmeticFunction.Moebius in
/-- The coprimality indicator as a Möbius sum over the divisors of the gcd. -/
theorem sum_moebius_gcd (a b : ℕ) :
    ∑ d ∈ (Nat.gcd a b).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      if Nat.Coprime a b then 1 else 0 := by
  have h := sum_moebius_divisors (Nat.gcd a b)
  have h' : ((∑ d ∈ (Nat.gcd a b).divisors, ArithmeticFunction.moebius d : ℤ) : ℂ)
      = ((if Nat.gcd a b = 1 then 1 else 0 : ℤ) : ℂ) := by rw [h]
  push_cast at h'
  rw [h']

/-- Reindexing a sum over the multiples of `d` in `[1, q]`. -/
theorem sum_Icc_filter_dvd {q d : ℕ} (hd : d ∣ q) (hd0 : 0 < d) (f : ℕ → ℂ) :
    ∑ h ∈ (Finset.Icc 1 q).filter (fun h => d ∣ h), f h
      = ∑ a ∈ Finset.Icc 1 (q / d), f (d * a) := by
  have himg : (Finset.Icc 1 (q / d)).image (fun a => d * a) = (Finset.Icc 1 q).filter (fun h => d ∣ h) := by
    ext h
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      have hqd : d * (q / d) = q := Nat.mul_div_cancel' hd
      refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨a, rfl⟩⟩
    · rintro ⟨⟨hh1, hh2⟩, ⟨a, rfl⟩⟩
      have ha0 : a ≠ 0 := by rintro rfl; simp at hh1
      have hda : d ≤ d * a := Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero ha0)
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · exact Nat.one_le_iff_ne_zero.mpr ha0
      · exact (Nat.le_div_iff_mul_le hd0).mpr (by nlinarith)
  rw [← himg, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd0 hab

/-- The character value at `0` kills the end points, so the `Icc` sum is the `range` sum. -/
theorem sum_Icc_chi_mul_e_eq_range {r s : ℕ} [NeZero r] (hr2 : 2 ≤ r)
    (χ : DirichletCharacter ℂ r) (m : ℤ) :
    ∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = ∑ a ∈ Finset.range (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
  haveI : Fact (1 < r) := ⟨by omega⟩
  have hzero : χ ((0 : ℕ) : ZMod r) = 0 := by
    have h : ((0 : ℕ) : ZMod r) = 0 := by simp
    rw [h, MulChar.map_zero]
  have hlast : χ (((r * s : ℕ)) : ZMod r) * e (((r * s : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) = 0 := by
    have h1 : ((r * s : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [h1, MulChar.map_zero, zero_mul]
  have hstep : ∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = ∑ a ∈ Finset.range (r * s + 1), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
    rw [← Finset.sum_filter_of_ne (s := Finset.range (r * s + 1))
      (f := fun a => χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
      (p := fun a => 1 ≤ a) ?_]
    · congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨fun h => ⟨Nat.lt_succ_of_le h.2, h.1⟩, fun h => ⟨h.2, Nat.le_of_lt_succ h.1⟩⟩
    · intro a ha hne
      by_contra h1
      have : a = 0 := by
        simp only [Finset.mem_range] at ha
        omega
      exact hne (by rw [this, hzero, zero_mul])
  rw [hstep, Finset.sum_range_succ, hlast, add_zero]

/-- **The inner sum in `Icc` form** (the shape the lab's `cRam` produces). -/
theorem norm_sum_Icc_chi_mul_e_le {r s : ℕ} [NeZero r] (hr2 : 2 ≤ r) (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  rw [sum_Icc_chi_mul_e_eq_range hr2 χ m]
  exact norm_sum_range_chi_mul_e_le hs hχ m


/-! ### The value of an induced character -/

theorem changeLevel_apply {n m : ℕ} (hm : n ∣ m) [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ n) (x : ZMod m) :
    (χ.changeLevel hm) x = if IsUnit x then χ (ZMod.castHom hm (ZMod n) x) else 0 := by
  by_cases hu : IsUnit x
  · obtain ⟨u, rfl⟩ := hu
    rw [ite_eq_left (show IsUnit ((u : ZMod m)) from ⟨u, rfl⟩),
      DirichletCharacter.changeLevel_eq_cast_of_dvd]
    simp only [ZMod.castHom_apply]
  · rw [ite_eq_right hu, MulChar.map_nonunit _ hu]

theorem changeLevel_apply_natCast {n m : ℕ} (hm : n ∣ m) [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ n) (h : ℕ) :
    (χ.changeLevel hm) (h : ZMod m) = if IsUnit (h : ZMod m) then χ (h : ZMod n) else 0 := by
  rw [changeLevel_apply]
  have hcast : ZMod.castHom hm (ZMod n) (h : ZMod m) = (h : ZMod n) := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hm h]
  rw [hcast]

/-! ### Removing the unit condition -/

/-- For a character mod `r` and `r ∣ q`, the induced character's value at `h` is the character
value at `h mod r` when `h` is a unit mod `q` and zero otherwise; the coprimality condition
`(h, q) = 1` may be replaced by `(h, q/r) = 1`. -/
theorem chi_mul_unit_eq_chi_mul_coprime {r s : ℕ} [NeZero r] [NeZero (r * s)]
    {χ : DirichletCharacter ℂ r} (h : ℕ) :
    χ (h : ZMod r) * (if IsUnit (h : ZMod (r * s)) then (1 : ℂ) else 0)
      = χ (h : ZMod r) * (if Nat.Coprime h s then (1 : ℂ) else 0) := by
  by_cases hχ : χ (h : ZMod r) = 0
  · rw [hχ, zero_mul, zero_mul]
  · have hunit : IsUnit (h : ZMod r) := (MulChar.apply_ne_zero_iff (χ := χ)).mp hχ
    have hcop : Nat.Coprime h r := (ZMod.isUnit_iff_coprime h r).mp hunit
    have key : IsUnit (h : ZMod (r * s)) ↔ Nat.Coprime h s := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
      exact ⟨fun h' => h'.2, fun h' => ⟨hcop, h'⟩⟩
    by_cases h2 : Nat.Coprime h s
    · rw [ite_eq_left (key.mpr h2), ite_eq_left h2]
    · rw [ite_eq_right (fun h1 => h2 (key.mp h1)), ite_eq_right h2]

/-- The divisors of a gcd, as the divisors of the second argument cut down by divisibility of
the first. -/
theorem divisors_gcd_eq (h s : ℕ) (hs : s ≠ 0) :
    (Nat.gcd h s).divisors = s.divisors.filter (fun d => d ∣ h) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  have hg : Nat.gcd h s ≠ 0 := by
    rintro h0
    exact hs (Nat.gcd_eq_zero_iff.mp h0).2
  constructor
  · rintro ⟨⟨hd1, hd2⟩, -⟩
    exact ⟨⟨hd2, hs⟩, hd1⟩
  · rintro ⟨⟨hd2, -⟩, hd1⟩
    exact ⟨⟨hd1, hd2⟩, hg⟩

/-- The coprimality indicator as a Möbius sum over the divisors of `s` alone. -/
theorem sum_moebius_of_coprime {h s : ℕ} (hs : s ≠ 0) :
    ∑ d ∈ s.divisors, (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)
      = if Nat.Coprime h s then (1 : ℂ) else 0 := by
  rw [← sum_moebius_gcd h s, ← Finset.sum_filter, divisors_gcd_eq h s hs]

/-! ### The Möbius decomposition of the coefficient sum -/

/-- The value of the induced character against the coprimality indicator. -/
theorem changeLevel_apply_natCast' {r s : ℕ} [NeZero r] [NeZero (r * s)]
    (χ : DirichletCharacter ℂ r) (h : ℕ) :
    (χ.changeLevel (Nat.dvd_mul_right r s)) (h : ZMod (r * s))
      = χ (h : ZMod r) * (if Nat.Coprime h s then (1 : ℂ) else 0) := by
  rw [changeLevel_apply_natCast]
  have hsplit : (if IsUnit (h : ZMod (r * s)) then χ (h : ZMod r) else 0)
      = χ (h : ZMod r) * (if IsUnit (h : ZMod (r * s)) then (1 : ℂ) else 0) := by
    by_cases hu : IsUnit (h : ZMod (r * s))
    · rw [ite_eq_left hu, ite_eq_left hu, mul_one]
    · rw [ite_eq_right hu, ite_eq_right hu, mul_zero]
  rw [hsplit, chi_mul_unit_eq_chi_mul_coprime]

set_option maxHeartbeats 1000000 in
/-- **The Möbius decomposition**: the coefficient sum of a character induced from level `r` to
level `r * s` is a `μ`-sum over the divisors of `s` of the shifted sums at the reduced levels. -/
theorem cRam_changeLevel_eq (r s : ℕ) [NeZero r] [NeZero (r * s)] (hs : 0 < s)
    (χ : DirichletCharacter ℂ r) (m : ℤ) :
    cRam (r * s) (χ.changeLevel (Nat.dvd_mul_right r s)) m
      = ∑ d ∈ s.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ (d : ZMod r) *
          ∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
            e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ)) := by
  have hsne : s ≠ 0 := hs.ne'
  have hF : ∀ h : ℕ, (χ.changeLevel (Nat.dvd_mul_right r s)) (h : ZMod (r * s)) *
      e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = χ (h : ZMod r) * (∑ d ∈ s.divisors,
          (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)) *
        e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
    intro h
    rw [changeLevel_apply_natCast' χ h, ← sum_moebius_of_coprime (h := h) hsne]
  have hswap : ∀ h : ℕ, χ (h : ZMod r) * (∑ d ∈ s.divisors,
        (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0)) *
        e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = ∑ d ∈ s.divisors, (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) *
          (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))) := by
    intro h
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  unfold cRam
  simp_rw [hF, hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ r * s := Dvd.dvd.mul_left (Nat.dvd_of_mem_divisors hd) r
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hs
  have hqf : ((r * s) / d) * d = r * s := Nat.div_mul_cancel hdvd
  -- turn the indicator into a filter and pull out the Möbius factor
  have hdist : ∀ h : ℕ, (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) *
        (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
      = (if d ∣ h then (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))) else 0) := by
    intro h
    by_cases hdiv : d ∣ h <;> simp [hdiv]
  have hstep : ∑ h ∈ Finset.Icc 1 (r * s),
        (if d ∣ h then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) *
          (χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)))
      = ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ h ∈ (Finset.Icc 1 (r * s)).filter (fun h => d ∣ h),
            χ (h : ZMod r) * e ((h : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)) := by
    simp_rw [hdist]
    rw [← Finset.sum_filter, Finset.mul_sum]
  rw [hstep, sum_Icc_filter_dvd hdvd hdpos]
  have hinner : ∑ a ∈ Finset.Icc 1 ((r * s) / d),
        χ ((d * a : ℕ) : ZMod r) * e (((d * a : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))
      = χ (d : ZMod r) * ∑ a ∈ Finset.Icc 1 ((r * s) / d),
          χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hchi : ((d * a : ℕ) : ZMod r) = (d : ZMod r) * (a : ZMod r) := by push_cast; ring
    have hev : ((d * a : ℕ) : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ)
        = (a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ) := by
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hrs0 : 0 < r * s := Nat.mul_pos (NeZero.pos r) hs
      have hq0 : 0 < (r * s) / d := Nat.div_pos (Nat.le_of_dvd hrs0 hdvd) hdpos
      have hqR : (((r * s) / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      have hrsR : ((r * s : ℕ) : ℝ) ≠ 0 := by positivity
      have hcast : ((r * s : ℕ) : ℝ) = (((r * s) / d : ℕ) : ℝ) * (d : ℝ) := by
        conv_lhs => rw [← hqf]
        push_cast
        ring
      have h1 : ((d * a : ℕ) : ℝ) = (d : ℝ) * (a : ℝ) := by push_cast; ring
      rw [h1, hcast]
      field_simp
    rw [hchi, hev, map_mul]
    ring
  rw [hinner]
  ring

/-- A character value has norm at most one. -/
theorem norm_apply_le_one {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (x : ZMod r) :
    ‖χ x‖ ≤ 1 := by
  by_cases hu : IsUnit x
  · have h := χ.unit_norm_eq_one hu.unit
    rw [hu.unit_spec] at h
    rw [h]
  · rw [MulChar.map_nonunit _ hu, norm_zero]
    exact zero_le_one

/-- **The coefficient sum of an induced character is `√r` times a divisor sum.** -/
theorem norm_cRam_changeLevel_le (r s : ℕ) [NeZero r] [NeZero (r * s)] (hr2 : 2 ≤ r)
    (hs : 0 < s) {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖cRam (r * s) (χ.changeLevel (Nat.dvd_mul_right r s)) m‖
      ≤ Real.sqrt r * ∑ d ∈ s.divisors,
          (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
  have hsne : s ≠ 0 := hs.ne'
  rw [cRam_changeLevel_eq r s hs χ m]
  have hterm : ∀ d ∈ s.divisors,
      ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ (d : ZMod r) *
        ∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
    intro d hd
    have hds : d ∣ s := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hds hs
    have hdvd : d ∣ r * s := Dvd.dvd.mul_left hds r
    have hqf : ((r * s) / d) * d = r * s := Nat.div_mul_cancel hdvd
    have hqd : (r * s) / d = r * (s / d) := by
      have h1 : d * (s / d) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hds
      have h2 : d * ((r * s) / d) = d * (r * (s / d)) := by
        rw [Nat.mul_comm d, hqf]
        calc r * s = r * (d * (s / d)) := by rw [h1]
          _ = d * (r * (s / d)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hdpos h2
    have hs' : 0 < s / d := Nat.div_pos (Nat.le_of_dvd hs hds) hdpos
    have h3 : ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      rw [hqd]
      exact norm_sum_Icc_chi_mul_e_le hr2 hs' hχ m
    refine le_trans (norm_mul_le _ _) ?_
    rw [norm_mul]
    have h1 : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.cast_one]
      exact Int.cast_le.mpr ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖χ (d : ZMod r)‖ ≤ 1 := norm_apply_le_one χ _
    have hnn : (0 : ℝ) ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      refine mul_nonneg (Real.sqrt_nonneg _) ?_
      split_ifs with h
      · positivity
      · exact le_rfl
    calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖χ (d : ZMod r)‖ *
          ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
            e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ 1 * 1 * (Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0)) := by
          refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) ?_
          positivity
      _ = Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by ring
  refine le_trans (norm_sum_le_of_le _ hterm) ?_
  rw [Finset.mul_sum]


/-! ### The level-one case and the unified inner bound -/

/-- At level one the inner sum is a geometric sum. -/
theorem sum_Icc_one_eq (s : ℕ) (hs : 0 < s) (m : ℤ) :
    ∑ a ∈ Finset.Icc 1 s, e ((a : ℝ) * (m : ℝ) / (s : ℝ))
      = e ((m : ℝ) / (s : ℝ)) * ∑ b ∈ Finset.range s, e ((b : ℝ) * (m : ℝ) / (s : ℝ)) := by
  have hIcc : Finset.Icc 1 s = Finset.Ico 1 (s + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsub : s + 1 - 1 = s := by omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range, hsub, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have harg : ((1 + b : ℕ) : ℝ) * (m : ℝ) / (s : ℝ)
      = (m : ℝ) / (s : ℝ) + (b : ℝ) * (m : ℝ) / (s : ℝ) := by
    push_cast
    ring
  rw [harg, e_add]

theorem norm_sum_Icc_one_le (s : ℕ) (hs : 0 < s) (m : ℤ) :
    ‖∑ a ∈ Finset.Icc 1 s, e ((a : ℝ) * (m : ℝ) / (s : ℝ))‖
      ≤ Real.sqrt 1 * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  rw [Real.sqrt_one, one_mul, sum_Icc_one_eq s hs m, norm_mul, norm_e, one_mul]
  by_cases hd : (s : ℤ) ∣ m
  · rw [ite_eq_left hd, sum_range_e_div_eq_card hs hd, Complex.norm_natCast]
  · rw [ite_eq_right hd, sum_range_e_div_eq_zero hs hd, norm_zero]

/-- **The inner sum, level one included.** -/
theorem norm_sum_Icc_chi_mul_e_le' {r s : ℕ} [NeZero r] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖∑ a ∈ Finset.Icc 1 (r * s), χ (a : ZMod r) * e ((a : ℝ) * (m : ℝ) / ((r * s : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if (s : ℤ) ∣ m then (s : ℝ) else 0) := by
  by_cases hr1 : r = 1
  · subst hr1
    haveI : Subsingleton (ZMod 1) := inferInstance
    have hfun : (fun a : ℕ => χ (a : ZMod 1) * e ((a : ℝ) * (m : ℝ) / (((1 * s : ℕ)) : ℝ)))
        = (fun a : ℕ => e ((a : ℝ) * (m : ℝ) / (s : ℝ))) := by
      funext a
      have h1 : χ (a : ZMod 1) = 1 := by
        rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ 1, map_one]
      have h2 : (((1 * s : ℕ)) : ℝ) = (s : ℝ) := by push_cast; ring
      rw [h1, one_mul, h2]
    rw [hfun, Nat.one_mul]
    simpa using norm_sum_Icc_one_le s hs m
  · have hr2 : 2 ≤ r := by
      have h1 : 0 < r := NeZero.pos r
      omega
    exact norm_sum_Icc_chi_mul_e_le hr2 hs hχ m

/-- **The coefficient sum of an induced character, level one included.** -/
theorem norm_cRam_changeLevel_le' (r s : ℕ) [NeZero r] [NeZero (r * s)] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) (m : ℤ) :
    ‖cRam (r * s) (χ.changeLevel (Nat.dvd_mul_right r s)) m‖
      ≤ Real.sqrt r * ∑ d ∈ s.divisors,
          (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
  rw [cRam_changeLevel_eq r s hs χ m]
  have hterm : ∀ d ∈ s.divisors,
      ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ (d : ZMod r) *
        ∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
      ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
    intro d hd
    have hds : d ∣ s := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hds hs
    have hdvd : d ∣ r * s := Dvd.dvd.mul_left hds r
    have hqf : ((r * s) / d) * d = r * s := Nat.div_mul_cancel hdvd
    have hqd : (r * s) / d = r * (s / d) := by
      have h1 : d * (s / d) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hds
      have h2 : d * ((r * s) / d) = d * (r * (s / d)) := by
        rw [Nat.mul_comm d, hqf]
        calc r * s = r * (d * (s / d)) := by rw [h1]
          _ = d * (r * (s / d)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hdpos h2
    have hs' : 0 < s / d := Nat.div_pos (Nat.le_of_dvd hs hds) hdpos
    have h3 : ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
          e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      rw [hqd]
      exact norm_sum_Icc_chi_mul_e_le' hs' hχ m
    have h1 : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.cast_one]
      exact Int.cast_le.mpr ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖χ (d : ZMod r)‖ ≤ 1 := norm_apply_le_one χ _
    have hnn : (0 : ℝ) ≤ Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by
      refine mul_nonneg (Real.sqrt_nonneg _) ?_
      split_ifs with h
      · positivity
      · exact le_rfl
    refine le_trans (norm_mul_le _ _) ?_
    rw [norm_mul]
    calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖χ (d : ZMod r)‖ *
          ‖∑ a ∈ Finset.Icc 1 ((r * s) / d), χ (a : ZMod r) *
            e ((a : ℝ) * (m : ℝ) / (((r * s) / d : ℕ) : ℝ))‖
        ≤ 1 * 1 * (Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0)) := by
          refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) ?_
          positivity
      _ = Real.sqrt r * (if ((s / d : ℕ) : ℤ) ∣ m then ((s / d : ℕ) : ℝ) else 0) := by ring
  refine le_trans (norm_sum_le_of_le _ hterm) ?_
  rw [Finset.mul_sum]

/-- The `m = 1` case: the Gauss sum of an induced character has the size of the conductor. -/
theorem norm_tau_changeLevel_le (r s : ℕ) [NeZero r] [NeZero (r * s)] (hs : 0 < s)
    {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) :
    ‖tau (r * s) (χ.changeLevel (Nat.dvd_mul_right r s))‖ ≤ Real.sqrt r := by
  have h := norm_cRam_changeLevel_le' r s hs hχ (1 : ℤ)
  have h0 : ∀ b ∈ s.divisors,
      b ≠ s → (if ((s / b : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / b : ℕ) : ℝ) else 0) = 0 := by
    intro d hd hds
    have hds' : d ∣ s := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hds' hs
    have hne : s / d ≠ 1 := by
      intro h1
      have h2 : d * (s / d) = d * 1 := by rw [h1]
      rw [Nat.mul_comm d, Nat.div_mul_cancel hds', mul_one] at h2
      exact hds h2.symm
    have : ¬ ((s / d : ℕ) : ℤ) ∣ (1 : ℤ) := by
      intro hdvd
      have h2 : (s / d : ℕ) ∣ 1 := by exact_mod_cast hdvd
      exact hne (Nat.dvd_one.mp h2)
    rw [ite_eq_right this]
  have h1 : s ∉ s.divisors →
      (if ((s / s : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / s : ℕ) : ℝ) else 0) = 0 := by
    intro hnot
    exact absurd (Nat.mem_divisors_self s hs.ne') hnot
  have hsum : ∑ d ∈ s.divisors,
      (if ((s / d : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / d : ℕ) : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (s := s.divisors)
      (f := fun d => (if ((s / d : ℕ) : ℤ) ∣ (1 : ℤ) then ((s / d : ℕ) : ℝ) else 0)) s h0 h1,
      Nat.div_self hs]
    norm_num
  rw [hsum, mul_one] at h
  simpa only [tau] using h


/-! ### The divisor sum and the inverse character -/

/-- The divisor sum of the induced-character bound is at most the sum of the divisors of `m`. -/
theorem sum_ite_dvd_le_divisors_sum {s m : ℕ} (hm : 0 < m) :
    ∑ d ∈ s.divisors, (if ((s / d : ℕ) : ℤ) ∣ (m : ℤ) then ((s / d : ℕ) : ℝ) else 0)
      ≤ ∑ e ∈ m.divisors, (e : ℝ) := by
  have hinj : ∀ a ∈ s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ)),
      ∀ b ∈ s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ)),
      s / a = s / b → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    have hda : a ∣ s := Nat.dvd_of_mem_divisors ha.1
    have hdb : b ∣ s := Nat.dvd_of_mem_divisors hb.1
    have hsne : s ≠ 0 := (Nat.mem_divisors.mp ha.1).2
    have hspos : 0 < s := Nat.pos_of_ne_zero hsne
    have h1 : a * (s / a) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hda
    have h2 : b * (s / b) = s := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdb
    have hsa : 0 < s / a := Nat.div_pos (Nat.le_of_dvd hspos hda) (Nat.pos_of_dvd_of_pos hda hspos)
    have hkey : a * (s / a) = b * (s / a) := by rw [h1, hab, h2]
    exact Nat.eq_of_mul_eq_mul_right hsa hkey
  rw [← Finset.sum_filter]
  rw [show (∑ d ∈ s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ)), ((s / d : ℕ) : ℝ))
      = ∑ e ∈ (s.divisors.filter (fun d => ((s / d : ℕ) : ℤ) ∣ (m : ℤ))).image
          (fun d => s / d), (e : ℝ) from by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj a ha b hb hab]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro e he
    simp only [Finset.mem_image, Finset.mem_filter] at he
    obtain ⟨d, ⟨hd, hdvd⟩, rfl⟩ := he
    have hdm : (s / d : ℕ) ∣ m := by exact_mod_cast hdvd
    exact Nat.mem_divisors.mpr ⟨hdm, hm.ne'⟩
  · intro e _ _
    exact Nat.cast_nonneg e

/-- An inverse character factors through the same levels. -/
theorem factorsThrough_inv {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} {d : ℕ}
    (h : χ⁻¹.FactorsThrough d) : χ.FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  refine ⟨hd, χ₀⁻¹, ?_⟩
  have hinv := congrArg (fun y : DirichletCharacter ℂ n => y⁻¹) hχ
  rw [inv_inv, ← map_inv] at hinv
  exact hinv

theorem factorsThrough_inv_iff {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} {d : ℕ} :
    χ⁻¹.FactorsThrough d ↔ χ.FactorsThrough d := by
  constructor
  · exact factorsThrough_inv
  · intro h
    exact factorsThrough_inv (χ := χ⁻¹) (by simpa using h)

theorem conductor_inv {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    (χ⁻¹).conductor = χ.conductor := by
  have h1 : (χ⁻¹).conductor ∣ χ.conductor :=
    (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ := χ⁻¹) (d := χ.conductor)
      χ.conductor_dvd_level).mp (factorsThrough_inv_iff.mpr χ.factorsThrough_conductor)
  have h2 : χ.conductor ∣ (χ⁻¹).conductor :=
    (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ := χ) (d := (χ⁻¹).conductor)
      (χ⁻¹).conductor_dvd_level).mp (factorsThrough_inv_iff.mp (χ⁻¹).factorsThrough_conductor)
  exact Nat.dvd_antisymm h1 h2

theorem isPrimitive_inv {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r} (h : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def] at h ⊢
  rw [conductor_inv]
  exact h

/-- A product of characters that both factor through `d` factors through `d`. -/
theorem factorsThrough_mul {n : ℕ} [NeZero n] {χ ψ : DirichletCharacter ℂ n} {d : ℕ}
    (hχ : χ.FactorsThrough d) (hψ : ψ.FactorsThrough d) : (χ * ψ).FactorsThrough d := by
  obtain ⟨hd, χ₀, rfl⟩ := hχ
  obtain ⟨hd', ψ₀, rfl⟩ := hψ
  exact ⟨hd, χ₀ * ψ₀, by rw [map_mul]⟩

/-- The conductor of a product of characters that factor through `L` divides `L`. -/
theorem conductor_mul_dvd {n L : ℕ} [NeZero n] {χ ψ : DirichletCharacter ℂ n}
    (hL : L ∣ n) (hχ : χ.FactorsThrough L) (hψ : ψ.FactorsThrough L) :
    (χ * ψ).conductor ∣ L :=
  (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ := χ * ψ) (d := L) hL).mp
    (factorsThrough_mul hχ hψ)


/-! ### The majorant and the totient lower bound (ported from the earlier sessions) -/


theorem log_natCast_le_eight_rpow {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h8 : (0 : ℝ) < (n : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hkey : Real.log (n : ℝ) = 8 * Real.log ((n : ℝ) ^ (1 / 8 : ℝ)) := by
    rw [Real.log_rpow hpos (1 / 8)]
    ring
  rw [hkey]
  have := Real.log_le_sub_one_of_pos h8
  linarith

theorem one_add_log_sq_le_rpow {n : ℕ} (hn : 1 ≤ n) :
    (1 + Real.log (n : ℝ)) ^ 2 ≤ 81 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hX1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hXpos : (0 : ℝ) < (n : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hlog : Real.log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := log_natCast_le_eight_rpow hn
  have hnn : (0 : ℝ) ≤ 1 + Real.log (n : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
    linarith
  have h9 : (0 : ℝ) ≤ 9 * (n : ℝ) ^ (1 / 8 : ℝ) := by positivity
  have hle : 1 + Real.log (n : ℝ) ≤ 9 * (n : ℝ) ^ (1 / 8 : ℝ) := by linarith
  have h2 : (1 + Real.log (n : ℝ)) ^ 2 ≤ (9 * (n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hnn hle 2
  have hsq : ((n : ℝ) ^ (1 / 8 : ℝ)) * ((n : ℝ) ^ (1 / 8 : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  calc (1 + Real.log (n : ℝ)) ^ 2 ≤ (9 * (n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := h2
    _ = 81 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        have hsq' : ((n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [pow_two, hsq]
        rw [mul_pow, hsq']
        norm_num

open LeanLab.PNTPort.LargeSieve in
theorem summable_nat_rpow_mul_one_add_log_sq :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (n : ℝ)) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (81 : ℝ) * (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ))) := by
    have h := (summable_nat_add_iff 1).mpr
      ((summable_nat_rpow.mpr (by norm_num : -(5 / 4 : ℝ) < -1)).mul_left (81 : ℝ))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_norm_bounded (g := fun n : ℕ =>
    (81 : ℝ) * (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ))) hbase ?_
  intro n
  have hn : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hpos.le _) (sq_nonneg _))]
  have hlog := one_add_log_sq_le_rpow hn
  have hkey : (((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) * ((((n + 1 : ℕ)) : ℝ) ^ (1 / 4 : ℝ)) =
      (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hpos]
    norm_num
  calc (((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (((n + 1 : ℕ)) : ℝ)) ^ 2
      ≤ (((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) *
          (81 * (((n + 1 : ℕ)) : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hpos.le _)
    _ = 81 * ((((n + 1 : ℕ)) : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((n + 1 : ℕ)) : ℝ) ^ (1 / 4 : ℝ)) := by ring
    _ = 81 * (((n + 1 : ℕ)) : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [hkey]

/-! ### From the pointwise bound to the leaf -/

/-- The product bound: `∏ p ≤ (|s| + 1) ∏ (p - 1)`, i.e. `∏ p/(p - 1) ≤ |s| + 1`. Induction on the maximum element:
removing `a` leaves `|s| - 1` elements, all `≥ 2` and `< a`, so `a ≥ |s| + 1`, and `a ≥ |s| + 1` is
exactly what `a·|s| ≤ (|s| + 1)(a - 1)` needs. -/
theorem prod_le_card_succ_mul_prod_pred {s : Finset ℕ} (h2 : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  revert h2
  refine Finset.induction_on_max s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h2
    have h2a : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
    have han : a ∉ s := fun h => absurd (ha a h) (lt_irrefl a)
    have hP := ih h2s
    have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨h2s x hx, by have := ha x hx; omega⟩
    have hcard : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have ham : s.card + 2 ≤ a := by omega
    obtain ⟨t, ht⟩ : ∃ t, a = s.card + 2 + t := ⟨a - (s.card + 2), by omega⟩
    have ha1 : a - 1 = s.card + 1 + t := by omega
    rw [Finset.prod_insert han, Finset.prod_insert han, Finset.card_insert_of_notMem han, ha1, ht]
    calc (s.card + 2 + t) * ∏ p ∈ s, p
        ≤ (s.card + 2 + t) * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
          Nat.mul_le_mul_left _ hP
      _ = ((s.card + 2 + t) * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by ring
      _ ≤ ((s.card + 1 + 1) * (s.card + 1 + t)) * ∏ p ∈ s, (p - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          nlinarith
      _ = (s.card + 1 + 1) * ((s.card + 1 + t) * ∏ p ∈ s, (p - 1)) := by ring

/-- `n ≤ φ(n) * (number of distinct prime divisors of n + 1)`. -/
theorem totient_mul_card_succ_ge (n : ℕ) :
    n ≤ Nat.totient n * (n.primeFactors.card + 1) := by
  have hid := Nat.totient_mul_prod_primeFactors n
  have hP : ∏ p ∈ n.primeFactors, p ≤
      (n.primeFactors.card + 1) * ∏ p ∈ n.primeFactors, (p - 1) :=
    prod_le_card_succ_mul_prod_pred fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * (n.primeFactors.card + 1)) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * ((n.primeFactors.card + 1) *
            ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hP
      _ = (Nat.totient n * (n.primeFactors.card + 1)) *
            ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

theorem totient_ge_div_card_succ (n : ℕ) :
    (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) ≤ (Nat.totient n : ℝ) := by
  have h := totient_mul_card_succ_ge n
  have hc : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hc]
  have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * ((n.primeFactors.card : ℝ) + 1) := by
    exact_mod_cast h
  linarith

theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, 2 ≤ p) → 2 ^ s.card ≤ ∏ p ∈ s, p := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro hs
        have h2a : 2 ≤ a := hs a (Finset.mem_insert_self a s)
        have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
        calc 2 ^ s.card * 2 ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul (ih h2s) h2a
          _ = a * ∏ p ∈ s, p := by ring
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    key _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : 0 < n := by omega
  exact h1.trans (Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd n))

theorem card_primeFactors_le_log_div {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 := two_pow_card_primeFactors_le hn
  have h2' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast h2
  have hbase : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hlog := Real.log_le_log hbase h2'
  rw [Real.log_pow] at hlog
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  linarith

/-- **`φ(n) ≫ n / log n`**: `log 2 · n / (1 + log n) ≤ φ(n)` for `n ≥ 1`, the shape the coefficient
bound `‖c'‖ ≪ q^{-3/2} (1 + log q)^2` needs. -/
theorem totient_ge_log_two_mul_div {n : ℕ} (hn : 1 ≤ n) :
    Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤ (Nat.totient n : ℝ) := by
  have hφ := totient_ge_div_card_succ n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlog1 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := card_primeFactors_le_log_div hn
  -- `k + 1 ≤ (1 + log n) / log 2`
  have hk2 : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [le_div_iff₀ hlog2] at hk
    linarith
  have hk1 : ((n.primeFactors.card : ℝ) + 1) * Real.log 2 ≤ 1 + Real.log n := by
    nlinarith [hk2, hlog2lt]
  have hone : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  -- `log 2 · n / (1 + log n) ≤ n / (k + 1)`
  have hstep : Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤
      (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + Real.log n) hone]
    nlinarith [hk1, hnpos, hlog2]
  exact hstep.trans hφ


/- `DecidableEq ExcPair` has no global instance (a `DirichletCharacter` field), so the `Finset`
operations below need Mathlib's existing `Classical.propDecidable` activated locally.  This declares
no instance; it is the idiom `State1581`/`DecompJ281` already use. -/
attribute [local instance] Classical.propDecidable

/-! ### The induced lift and its inverse -/


/-- **The induced-character bound at an arbitrary level**, with the level ratio `q / r`. -/
theorem norm_cRam_changeLevel_gen {r q : ℕ} [NeZero r] [NeZero q] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (h : r ∣ q) (m : ℤ) :
    ‖cRam q (χ.changeLevel h) m‖
      ≤ Real.sqrt r * ∑ d ∈ (q / r).divisors,
          (if (((q / r) / d : ℕ) : ℤ) ∣ m then (((q / r) / d : ℕ) : ℝ) else 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, q = r * s := ⟨q / r, (Nat.mul_div_cancel' h).symm⟩
  have hq0 : 0 < r * s := NeZero.pos (r * s)
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, Nat.mul_zero] at hq0
      exact absurd hq0 (lt_irrefl 0)
    · exact h0
  have h' : h = Nat.dvd_mul_right r s := Subsingleton.elim _ _
  have hqr : (r * s) / r = s := Nat.mul_div_right s (NeZero.pos r)
  rw [h', hqr]
  exact norm_cRam_changeLevel_le' r s hs hχ m

/-- **The Gauss sum of an induced character at an arbitrary level.** -/
theorem lift_eq_changeLevel' (z : ExcPair) {q : ℕ} (hq : z.r ∣ q) :
    lift z q = DirichletCharacter.changeLevel hq z.χ := by
  unfold LeanLab.Pintz2021.State1581.lift
  rw [dif_pos hq]

theorem norm_tau_changeLevel_gen {r q : ℕ} [NeZero r] [NeZero q] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (h : r ∣ q) :
    ‖tau q (χ.changeLevel h)‖ ≤ Real.sqrt (r : ℝ) := by
  obtain ⟨s, rfl⟩ : ∃ s, q = r * s := ⟨q / r, (Nat.mul_div_cancel' h).symm⟩
  have hq0 : 0 < r * s := NeZero.pos (r * s)
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, Nat.mul_zero] at hq0
      exact absurd hq0 (lt_irrefl 0)
    · exact h0
  have h' : h = Nat.dvd_mul_right r s := Subsingleton.elim _ _
  rw [h']
  exact norm_tau_changeLevel_le r s hs hχ

/-- The Gauss sum of the inverse lift has the size of the conductor. -/
theorem norm_tau_lift_inv_le (z : ExcPair) (hz : z.χ.IsPrimitive) (q : ℕ) (hq : 0 < q)
    (hqr : z.r ∣ q) :
    ‖tau q (lift z q)⁻¹‖ ≤ Real.sqrt (z.r : ℝ) := by
  haveI : NeZero z.r := z.hr
  haveI : NeZero q := ⟨hq.ne'⟩
  rw [lift_eq_changeLevel' z hqr, ← map_inv]
  exact norm_tau_changeLevel_gen (isPrimitive_inv hz) hqr

/-- The coefficient sum of the product of a lift and an inverse lift. -/
theorem norm_cRam_lift_product_le (z w : ExcPair) (hz : z.χ.IsPrimitive)
    (hw : w.χ.IsPrimitive) (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 0 < q)
    (hL : Nat.lcm z.r w.r ∣ q) :
    ‖cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ))‖
      ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) := by
  haveI : NeZero z.r := z.hr
  haveI : NeZero w.r := w.hr
  haveI : NeZero q := ⟨hq.ne'⟩
  have hL0 : 0 < Nat.lcm z.r w.r := Nat.lcm_pos (NeZero.pos z.r) (NeZero.pos w.r)
  haveI : NeZero (Nat.lcm z.r w.r) := ⟨hL0.ne'⟩
  have hqr1 : z.r ∣ q := (Nat.dvd_lcm_left z.r w.r).trans hL
  have hqr2 : w.r ∣ q := (Nat.dvd_lcm_right z.r w.r).trans hL
  have hf1 : (lift z q).FactorsThrough (Nat.lcm z.r w.r) := by
    rw [lift_eq_changeLevel' z hqr1]
    exact DirichletCharacter.FactorsThrough.mono _
      (DirichletCharacter.changeLevel_factorsThrough z.χ hqr1)
      (Nat.dvd_lcm_left z.r w.r) hL
  have hf2 : ((lift w q)⁻¹).FactorsThrough (Nat.lcm z.r w.r) := by
    rw [lift_eq_changeLevel' w hqr2, ← map_inv]
    exact DirichletCharacter.FactorsThrough.mono _
      (DirichletCharacter.changeLevel_factorsThrough w.χ⁻¹ hqr2)
      (Nat.dvd_lcm_right z.r w.r) hL
  set ψ : DirichletCharacter ℂ q := lift z q * (lift w q)⁻¹ with hψdef
  have hcond : ψ.conductor ∣ Nat.lcm z.r w.r := conductor_mul_dvd hL hf1 hf2
  have hcondq : ψ.conductor ∣ q := hcond.trans hL
  have hcond0 : ψ.conductor ≠ 0 := ψ.conductor_ne_zero
  have hψpc : DirichletCharacter.changeLevel hcondq ψ.primitiveCharacter = ψ :=
    ψ.changeLevel_primitiveCharacter
  have hcr : ‖cRam q ψ (-(m : ℤ))‖ ≤ Real.sqrt (ψ.conductor : ℝ) *
      ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ (-(m : ℤ)) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0) := by
    have e : ‖cRam q ψ (-(m : ℤ))‖
        = ‖cRam q (DirichletCharacter.changeLevel hcondq ψ.primitiveCharacter) (-(m : ℤ))‖ := by
      rw [hψpc]
    rw [e]
    exact norm_cRam_changeLevel_gen ψ.primitiveCharacter_isPrimitive hcondq (-(m : ℤ))
  have hsum_eq : ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ (-(m : ℤ)) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0)
      = ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hdv : (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ)
    · rw [ite_eq_left (by rwa [Int.dvd_neg] : (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ -((m : ℕ) : ℤ)),
        ite_eq_left hdv]
    · rw [ite_eq_right (fun hh => hdv (by rwa [Int.dvd_neg] at hh)), ite_eq_right hdv]
  rw [hsum_eq] at hcr
  have hσ : ∑ d ∈ (q / ψ.conductor).divisors,
        (if (((q / ψ.conductor) / d : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ) then
          (((q / ψ.conductor) / d : ℕ) : ℝ) else 0)
      ≤ ∑ e ∈ m.divisors, (e : ℝ) := sum_ite_dvd_le_divisors_sum hm
  have hsqrt : Real.sqrt (ψ.conductor : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast Nat.le_of_dvd hL0 hcond
  have hnn : (0 : ℝ) ≤ ∑ e ∈ m.divisors, (e : ℝ) := by positivity
  calc ‖cRam q ψ (-(m : ℤ))‖
      ≤ Real.sqrt (ψ.conductor : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) := by
        refine le_trans hcr ?_
        exact mul_le_mul_of_nonneg_left hσ (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt hnn


/-- **The coefficient bound**: `‖c'(z,w,q,m)‖ ≪ q^{-3/2} (1 + log q)^2`, uniformly in `q` on the
multiples of the lcm of the conductors. -/
theorem norm_cCoefPrime_le (z w : ExcPair) (hz : z.χ.IsPrimitive) (hw : w.χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 1 ≤ q) (hL : Nat.lcm z.r w.r ∣ q) :
    ‖cCoefPrime z w q m‖ ≤
      ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 /
        (Real.log 2) ^ 2) * ((q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2) := by
  have hq0 : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  haveI : NeZero q := ⟨hq0.ne'⟩
  haveI : NeZero z.r := z.hr
  haveI : NeZero w.r := w.hr
  have hL0 : 0 < Nat.lcm z.r w.r := Nat.lcm_pos (NeZero.pos z.r) (NeZero.pos w.r)
  obtain ⟨h1, h2, h3⟩ : ‖cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ))‖ ≤
        Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ) ∧
      ‖tau q (lift z q)⁻¹‖ ≤ Real.sqrt (z.r : ℝ) ∧
      ‖tau q (lift w q)⁻¹‖ ≤ Real.sqrt (w.r : ℝ) :=
    ⟨norm_cRam_lift_product_le z w hz hw m hm q hq0 hL,
     norm_tau_lift_inv_le z hz q hq0 ((Nat.dvd_lcm_left z.r w.r).trans hL),
     norm_tau_lift_inv_le w hw q hq0 ((Nat.dvd_lcm_right z.r w.r).trans hL)⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : (0 : ℝ) < 1 + Real.log (q : ℝ) := by
    have := Real.log_nonneg hq1
    linarith
  have hσ : (0 : ℝ) ≤ ∑ e ∈ m.divisors, (e : ℝ) := by positivity
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have := Nat.totient_pos.mpr hq0
    exact_mod_cast this
  have hφlow : Real.log 2 * (q : ℝ) / (1 + Real.log (q : ℝ)) ≤ (Nat.totient q : ℝ) :=
    totient_ge_log_two_mul_div hq
  have hφlow0 : (0 : ℝ) < Real.log 2 * (q : ℝ) / (1 + Real.log (q : ℝ)) := by positivity
  have hφnorm : ‖((Nat.totient q : ℂ) ^ 2)⁻¹‖ = (((Nat.totient q : ℝ)) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  have hrec : 1 / (Nat.totient q : ℝ) ≤ (1 + Real.log (q : ℝ)) / (Real.log 2 * (q : ℝ)) := by
    rw [div_le_div_iff₀ hφpos (by positivity : (0 : ℝ) < Real.log 2 * (q : ℝ)), one_mul]
    have hmul := mul_le_mul_of_nonneg_right hφlow hlogq.le
    have hsimp : Real.log 2 * (q : ℝ) / (1 + Real.log (q : ℝ)) * (1 + Real.log (q : ℝ))
        = Real.log 2 * (q : ℝ) := by field_simp
    rw [hsimp] at hmul
    linarith
  have hφbound : (((Nat.totient q : ℝ)) ^ 2)⁻¹ ≤
      (1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2) := by
    have hsq : (1 / (Nat.totient q : ℝ)) ^ 2 ≤
        ((1 + Real.log (q : ℝ)) / (Real.log 2 * (q : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hrec 2
    have hrhs : ((1 + Real.log (q : ℝ)) / (Real.log 2 * (q : ℝ))) ^ 2
        = (1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2) := by
      rw [div_pow, mul_pow]
    rw [hrhs] at hsq
    calc (((Nat.totient q : ℝ)) ^ 2)⁻¹ = (1 / (Nat.totient q : ℝ)) ^ 2 := by
          rw [one_div, inv_pow]
      _ ≤ _ := hsq
  have hprod : ‖cCoefPrime z w q m‖ ≤ (((Nat.totient q : ℝ)) ^ 2)⁻¹ *
      ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ)) := by
    rw [cCoefPrime, norm_mul, norm_mul, norm_mul]
    rw [show (starRingEnd ℂ) (tau q (lift w q)⁻¹) = star (tau q (lift w q)⁻¹) from rfl, norm_star]
    rw [hφnorm]
    have hsqr1 : Real.sqrt (z.r : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast Nat.le_of_dvd hL0 (Nat.dvd_lcm_left z.r w.r)
    have hsqr2 : Real.sqrt (w.r : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast Nat.le_of_dvd hL0 (Nat.dvd_lcm_right z.r w.r)
    have hLnn : (0 : ℝ) ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := Real.sqrt_nonneg _
    have ht1 : ‖tau q (lift z q)⁻¹‖ ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := le_trans h2 hsqr1
    have ht2 : ‖tau q (lift w q)⁻¹‖ ≤ Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := le_trans h3 hsqr2
    have hφnn : (0 : ℝ) ≤ (((Nat.totient q : ℝ)) ^ 2)⁻¹ := by positivity
    calc (((((Nat.totient q : ℝ)) ^ 2)⁻¹ * ‖cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ))‖) *
          ‖tau q (lift z q)⁻¹‖) * ‖tau q (lift w q)⁻¹‖
        ≤ (((((Nat.totient q : ℝ)) ^ 2)⁻¹ *
            (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) * ∑ e ∈ m.divisors, (e : ℝ))) *
              Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) *
            Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ) := by
          refine mul_le_mul ?_ ht2 (norm_nonneg _) (by positivity)
          refine mul_le_mul ?_ ht1 (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left h1 hφnn
      _ = (((Nat.totient q : ℝ)) ^ 2)⁻¹ *
            ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ)) := by ring
  have hstep2 : ‖cCoefPrime z w q m‖ ≤
      ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) *
        ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) := by
    refine le_trans hprod ?_
    calc (((Nat.totient q : ℝ)) ^ 2)⁻¹ *
          ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ))
        ≤ ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) *
            ((Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 * ∑ e ∈ m.divisors, (e : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hφbound (by positivity)
      _ = ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) *
            ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) := by ring
  have hinv_le : 1 / (q : ℝ) ^ 2 ≤ (q : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have h1 : (q : ℝ) ^ (-(2 : ℝ)) ≤ (q : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have h2 : (q : ℝ) ^ (-(2 : ℝ)) = 1 / (q : ℝ) ^ 2 := by
      rw [Real.rpow_neg hqR.le, Real.rpow_two, one_div]
    rwa [h2] at h1
  have hsplit : ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) *
        ((1 + Real.log (q : ℝ)) ^ 2 / ((Real.log 2) ^ 2 * (q : ℝ) ^ 2))
      = (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
          (Real.log 2) ^ 2) * (1 / (q : ℝ) ^ 2) * (1 + Real.log (q : ℝ)) ^ 2 := by
    field_simp
  refine le_trans hstep2 ?_
  rw [hsplit]
  have h2' : (0 : ℝ) ≤ ((∑ e ∈ m.divisors, (e : ℝ)) *
      (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) / (Real.log 2) ^ 2 := by
    have := Real.sqrt_nonneg ((Nat.lcm z.r w.r : ℕ) : ℝ)
    positivity
  have h3' : (0 : ℝ) ≤ (1 + Real.log (q : ℝ)) ^ 2 := sq_nonneg _
  calc (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
        (Real.log 2) ^ 2) * (1 / (q : ℝ) ^ 2) * (1 + Real.log (q : ℝ)) ^ 2
      ≤ (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
          (Real.log 2) ^ 2) * (q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv_le h2') h3'
    _ = (((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3) /
          (Real.log 2) ^ 2) * ((q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2) := by
        ring


/-- Partial sums over `[1, Q]` converge for a summable sequence, with the `q = 0` term removed. -/
theorem tendsto_Icc_sum_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun Q : ℕ => ∑ q ∈ Finset.Icc 1 Q, f q) atTop (𝓝 ((∑' q, f q) - f 0)) := by
  have h1 : ∀ Q : ℕ, ∑ q ∈ Finset.Icc 1 Q, f q = (∑ q ∈ Finset.range (Q + 1), f q) - f 0 := by
    intro Q
    have hset : Finset.range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    ring
  have h2 : Tendsto (fun Q : ℕ => ∑ q ∈ Finset.range (Q + 1), f q) atTop (𝓝 (∑' q, f q)) :=
    hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [h1] using h2.sub_const (f 0)

/-- **The masked coefficient series is summable.** -/
theorem summable_masked_cCoefPrime (z w : ExcPair) (hz : z.χ.IsPrimitive)
    (hw : w.χ.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    Summable (fun q : ℕ => if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) := by
  set A : ℝ := (∑ e ∈ m.divisors, (e : ℝ)) *
    (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 / (Real.log 2) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    have := Real.sqrt_nonneg ((Nat.lcm z.r w.r : ℕ) : ℝ)
    positivity
  have hmaj : Summable (fun q : ℕ => A *
      (((q + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (((q + 1 : ℕ)) : ℝ)) ^ 2)) := by
    have hbase := summable_nat_rpow_mul_one_add_log_sq.mul_left A
    have hshift := (summable_nat_add_iff 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_norm_bounded (g := fun q : ℕ => A *
    (((q + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (((q + 1 : ℕ)) : ℝ)) ^ 2)) hmaj ?_
  intro q
  by_cases hd : Nat.lcm z.r w.r ∣ q + 1
  · rw [ite_eq_left hd]
    have hb := norm_cCoefPrime_le z w hz hw m hm (q + 1) (Nat.le_add_left 1 q) hd
    rw [hA]
    simpa only [Nat.cast_add, Nat.cast_one] using hb
  · rw [ite_eq_right hd, norm_zero]
    exact mul_nonneg hA0 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))

/-- Every point of the exceptional set carries a primitive character. -/
theorem isPrimitive_of_mem_excSet {H U P X : ℝ} {z : ExcPair} (hz : z ∈ excSet H U P X) :
    z.χ.IsPrimitive := by
  rcases Set.mem_insert_iff.mp hz with h | h
  · subst h
    exact DirichletCharacter.isPrimitive_one_level_one
  · exact h.2.1



/-! ### The size of the singular series

`leaf_truncation_error_3` compares the main term with its truncation on the pairs that the
`[r₁,r₂] ≤ P`, `|Im ϱ| ≤ U` cutoffs discard, so it needs the size of `𝔖'` on those pairs.  The
coefficient bound of the previous section gives it: the partial sums are bounded by the converging
majorant, uniformly in the cutoff `Q`. -/

/-- **The singular series is bounded by the coefficient majorant.** -/
theorem norm_Sg'_le (z w : ExcPair) (hz : z.χ.IsPrimitive) (hw : w.χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (Sg' : ExcPair → ExcPair → ℕ → ℂ)
    (hconv : Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) :
    ‖Sg' z w m‖ ≤
      ((∑ e ∈ m.divisors, (e : ℝ)) * (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 /
        (Real.log 2) ^ 2) *
        (∑' q : ℕ, (q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2) := by
  have hA0 : (0 : ℝ) ≤ (∑ e ∈ m.divisors, (e : ℝ)) *
      (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 / (Real.log 2) ^ 2 := by
    have := Real.sqrt_nonneg ((Nat.lcm z.r w.r : ℕ) : ℝ)
    positivity
  refine le_of_tendsto' hconv.norm ?_
  intro Q
  have hfun : singPartialPrime z w m Q = ∑ q ∈ Finset.Icc 1 Q,
      (if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) := by
    rw [singPartialPrime, ← Finset.sum_filter]
  rw [hfun]
  have hstep : ‖∑ q ∈ Finset.Icc 1 Q,
        (if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0)‖
      ≤ ∑ q ∈ Finset.Icc 1 Q, ((∑ e ∈ m.divisors, (e : ℝ)) *
          (Real.sqrt ((Nat.lcm z.r w.r : ℕ) : ℝ)) ^ 3 / (Real.log 2) ^ 2) *
            ((q : ℝ) ^ (-(3 / 2 : ℝ)) * (1 + Real.log (q : ℝ)) ^ 2) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q hq => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    by_cases hd : Nat.lcm z.r w.r ∣ q
    · rw [ite_eq_left hd]
      exact norm_cCoefPrime_le z w hz hw m hm q hq1 hd
    · rw [ite_eq_right hd, norm_zero]
      exact mul_nonneg hA0 (by positivity)
  refine le_trans hstep ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hA0
  exact Summable.sum_le_tsum (Finset.Icc 1 Q) (fun q _ => by positivity)
    summable_nat_rpow_mul_one_add_log_sq


/-- **The discarded mass is bounded by the multiplicity count** once the singular series is bounded
uniformly on the pairs of the exceptional set. -/
theorem mass_le_of_uniform_Sg {X K : ℝ} (hX : 0 ≤ X) {P U : ℝ} {m : ℕ}
    (Sg' : ExcPair → ExcPair → ℕ → ℂ) {E : Finset ExcPair}
    (hSg : ∀ z ∈ E, ∀ w ∈ E, ‖Sg' z w m‖ ≤ K) (hK : 0 ≤ K) :
    X * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg' p.1 p.2 m‖
      ≤ X * K * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) := by
  classical
  have hterm : ∀ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
      ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg' p.1 p.2 m‖ ≤
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * K := by
    intro p hp
    have hpE : p ∈ E ×ˢ E := Finset.mem_sdiff.mp hp |>.1
    have h1 : p.1 ∈ E := (Finset.mem_product.mp hpE).1
    have h2 : p.2 ∈ E := (Finset.mem_product.mp hpE).2
    exact mul_le_mul_of_nonneg_left (hSg p.1 h1 p.2 h2) (by positivity)
  have hstep := Finset.sum_le_sum hterm
  have h1 : X * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
      ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg' p.1 p.2 m‖
      ≤ X * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * K :=
    mul_le_mul_of_nonneg_left hstep hX
  calc X * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg' p.1 p.2 m‖
      ≤ X * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
          ((mult p.1 * mult p.2 : ℕ) : ℝ) * K := h1
    _ = X * K * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
          ((mult p.1 * mult p.2 : ℕ) : ℝ) := by
        rw [← Finset.sum_mul]
        ring

/-- **The repaired truncation leaf follows from a `uniform` singular series bound together with a
multiplicity count of the discarded pairs.** This is the exact shape of what display 10.27 still
needs: `norm_Sg'_le` supplies a bound that grows like `(√[r₁,r₂])³` with the conductors, while the
leaf's constant `C'` is independent of `P`, so a bound uniform over the pairs — i.e. the analytic
input of the paper — is still missing, and so is the pair count (an `N(T,χ)` estimate). -/
theorem leaf_truncation_error_3_of_uniform_mass
    (hinput : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
        Thm1Hyp ε H0 X0 H X P0 → 1 ≤ P → P ≤ P0 →
        (excSet H (Real.sqrt X) P X).Finite →
        (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
          Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
        X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
        ∀ E : Finset ExcPair, (E : Set ExcPair) = excSet H (Real.sqrt X) P X →
          ∃ K : ℝ, 0 ≤ K ∧ (∀ z ∈ E, ∀ w ∈ E, ‖Sg' z w m‖ ≤ K) ∧
            K * ∑ p ∈ (E ×ˢ E) \ LeanLab.Pintz2021.Truncation168.retainedPairs E P U m,
              ((mult p.1 * mult p.2 : ℕ) : ℝ) ≤
              C' * (Sing m * Real.log U / Real.sqrt U)) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
        Thm1Hyp ε H0 X0 H X P0 → 1 ≤ P → P ≤ P0 →
        (excSet H (Real.sqrt X) P X).Finite →
        (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
          Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
        X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
        ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
          mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
        C' * (Sing m * X * Real.log U / Real.sqrt U) := by
  classical
  obtain ⟨ε0, hε0, h⟩ := hinput
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hεlt
  obtain ⟨H0, C', X0, hC', hb⟩ := h ε hε hεlt
  refine ⟨H0, C', X0, hC', ?_⟩
  intro H X P0 P U Sg' m hHyp hP1 hP2 hFin hconv hm1 hm2 hU
  have hX : (0 : ℝ) ≤ X := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have herr := LeanLab.Pintz2021.DecompJ665.actual_truncation_error_le_mass (H := H) hX P U ε m Sg'
    hFin.toFinset hFin.coe_toFinset
  obtain ⟨K, hK, hSg, hcount⟩ :=
    hb H X P0 P U Sg' m hHyp hP1 hP2 hFin hconv hm1 hm2 hU hFin.toFinset hFin.coe_toFinset
  have hmass := mass_le_of_uniform_Sg (X := X) hX (P := P) (U := U) (m := m) Sg' hSg hK
  refine le_trans herr ?_
  calc X * ∑ p ∈ (hFin.toFinset ×ˢ hFin.toFinset) \
        LeanLab.Pintz2021.Truncation168.retainedPairs hFin.toFinset P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg' p.1 p.2 m‖
      ≤ X * K * ∑ p ∈ (hFin.toFinset ×ˢ hFin.toFinset) \
          LeanLab.Pintz2021.Truncation168.retainedPairs hFin.toFinset P U m,
          ((mult p.1 * mult p.2 : ℕ) : ℝ) := hmass
    _ = X * (K * ∑ p ∈ (hFin.toFinset ×ˢ hFin.toFinset) \
          LeanLab.Pintz2021.Truncation168.retainedPairs hFin.toFinset P U m,
          ((mult p.1 * mult p.2 : ℕ) : ℝ)) := by ring
    _ ≤ X * (C' * (Sing m * Real.log U / Real.sqrt U)) :=
        mul_le_mul_of_nonneg_left hcount hX
    _ = C' * (Sing m * X * Real.log U / Real.sqrt U) := by ring

end

/-! ### The leaves -/

/-- REFUTED, `DecompJ665.P_leaf_false`, no `0 < ε`. Repaired in `DecompJ579.leaf_P_exists`. Do not prove this.
LEAF arXiv:1804.05561v1 display 8.28: the major arc parameter P exists -/
theorem leaf_P_exists_3 {ε H0 X0 H X P0 : ℝ} (hHyp : Thm1Hyp ε H0 X0 H X P0) :
  ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by sorry

theorem leaf_singular_series_converges_3 (H X P : ℝ) :
    ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by
  refine ⟨fun z w m => (∑' q : ℕ, if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) -
    (if Nat.lcm z.r w.r ∣ 0 then cCoefPrime z w 0 m else 0), ?_⟩
  intro z hz w hw m hm
  have hf := summable_masked_cCoefPrime z w (isPrimitive_of_mem_excSet hz)
    (isPrimitive_of_mem_excSet hw) m hm
  have hconv := tendsto_Icc_sum_of_summable hf
  have hfun : singPartialPrime z w m = fun Q => ∑ q ∈ Finset.Icc 1 Q,
      if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0 := by
    funext Q
    rw [singPartialPrime, ← Finset.sum_filter]
  rw [hfun]
  exact hconv

/-- REFUTED given `leaf_singular_series_converges_3`, `Audit1614.old_leaf_main_term_bound_exists_C_false_of_converges`: `C` is universal, take `C = -1`. Use `DecompJ579.leaf_main_term_bound`. Do not prove this.
LEAF arXiv:1804.05561v1 display 10.25: the main term error is bounded by a constant C depending only on ε -/
theorem leaf_main_term_bound_exists_C_3 (ε ε0 c H0 C X0 : ℝ) :
  ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    Thm1Hyp ε H0 X0 H X P0 →
    P0 * X ^ (-ε) ≤ P → P ≤ P0 →
    (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
    ∀ m : ℕ, (m : ℝ) ≤ X → 0 < m →
      ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
        C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by sorry

/-- LEAF arXiv:1804.05561v1 display 8.28: the epsilon threshold and core constants exist -/
theorem leaf_constants_exist_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c := by
  exact ⟨1, one_pos, fun _ _ _ => ⟨1, 0, 0, 0, one_pos⟩⟩

/-- Assembly of Theorem 1 display 2.21 (untruncated form). -/
theorem assembly_321_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X → 0 < m →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by
  obtain ⟨ε0, hε0, h1⟩ := leaf_constants_exist_3
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  obtain ⟨c, H0, C, X0, hc⟩ := h1 ε hε hε0'
  refine ⟨c, H0, C, X0, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨P, hP1, hP2, hFin⟩ := leaf_P_exists_3 hHyp
  refine ⟨P, hP1, hP2, hFin, ?_⟩
  obtain ⟨Sg', hSg1⟩ := leaf_singular_series_converges_3 H X P
  refine ⟨Sg', hSg1, ?_⟩
  exact leaf_main_term_bound_exists_C_3 ε ε0 c H0 C X0 H X P0 P Sg' hHyp hP1 hP2 hSg1

/- REPAIRED 2026-11-05 lomos 20261105T1214Z: `1 ≤ P` added, the only change of statement in this
file. The former form assumed only `P ≤ P0`, and `DecompJ665.truncation_leaf281_false` (also
`DecompJ281Audit.leaf_truncation_error_false`) is a kernel-checked negation of it: at the level
`P = 0` the exceptional set `excSet H (√X) 0 X` is the pole alone, whose `Nat.lcm pole.r pole.r`
is `1 > P`, so the truncated sum vanishes at every cutoff `U`, the full sum keeps the pole term,
and the right hand side `C' * (Sing m * X * log U / √U)` tends to zero as `U → ∞`, so no constant
exists. The lower bound `1 ≤ P` is the paper's own requirement that the pole pair survive the
`[r₁, r₂] ≤ P` restriction (`DecompJ281.pole_lcm_retained`), and `assembly_322_3` supplies it at
`P = P0`, which lies in `[P0 X^{-ε}, P0]` once `X ≥ 1` because `Thm1Hyp` gives `1 ≤ P0`. The leaf
itself stays OPEN: display 10.27 needs the mass of the discarded pairs, which is not in Mathlib. -/
/-- LEAF arXiv:1804.05561v1 display 10.27: the truncated tail error is bounded, at arc levels
`1 ≤ P ≤ P0` -/
theorem leaf_truncation_error_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
      Thm1Hyp ε H0 X0 H X P0 → 1 ≤ P → P ≤ P0 →
      (excSet H (Real.sqrt X) P X).Finite →
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
        Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
      X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
      ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U) := by sorry

/-- LEAF Assembly of Theorem 1 display 2.22 (truncated form). -/
theorem assembly_322_3 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C C' X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, X / 4 ≤ m ∧ (m : ℝ) ≤ X / 2 →
            ‖R1majPrime ε X P m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P (Real.sqrt X) m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) + C' * (Sing m * X * Real.log (Real.sqrt X) / (Real.sqrt (Real.sqrt X))) := by
  obtain ⟨ε1, hε1, h1⟩ := leaf_constants_exist_3
  obtain ⟨ε2, hε2, h2⟩ := leaf_truncation_error_3
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro ε hε hεlt
  obtain ⟨c, H0a, Ca, X0a, hc⟩ := h1 ε hε (lt_of_lt_of_le hεlt (min_le_left ε1 ε2))
  obtain ⟨H0b, C', X0b, hC'⟩ := h2 ε hε (lt_of_lt_of_le hεlt (min_le_right ε1 ε2))
  refine ⟨c, max H0a H0b, Ca, C', max (max X0a X0b) 4, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨hH0, hHlog, hX0, hP01, hP0X⟩ := hHyp
  have hXa : X0a ≤ X := le_trans (le_trans (le_max_left X0a X0b) (le_max_left _ 4)) hX0
  have hXb : X0b ≤ X := le_trans (le_trans (le_max_right X0a X0b) (le_max_left _ 4)) hX0
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_right _ 4) hX0
  have hHA : Thm1Hyp ε H0a X0a H X P0 :=
    ⟨le_trans (le_max_left H0a H0b) hH0, hHlog, hXa, hP01, hP0X⟩
  have hHB : Thm1Hyp ε H0b X0b H X P0 :=
    ⟨le_trans (le_max_right H0a H0b) hH0, hHlog, hXb, hP01, hP0X⟩
  -- the level `P = P0` lies in `[P0 X^{-ε}, P0]`, and it is at least `1`, as the repaired
  -- truncation leaf requires and `Thm1Hyp` supplies
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlow : P0 * X ^ (-ε) ≤ P0 := by
    have hx : X ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
    calc P0 * X ^ (-ε) ≤ P0 * 1 := mul_le_mul_of_nonneg_left hx (by linarith)
      _ = P0 := mul_one P0
  have hFin : (excSet H (Real.sqrt X) P0 X).Finite := excSet_finite H (Real.sqrt X) P0 X
  obtain ⟨Sg', hSg⟩ := leaf_singular_series_converges_3 H X P0
  refine ⟨P0, hlow, le_rfl, hFin, Sg', hSg, ?_⟩
  intro m hm
  have hmX : (m : ℝ) ≤ X := by linarith [hm.2]
  have hmpos : 0 < m := by
    have h1m : (1 : ℝ) ≤ (m : ℝ) := by linarith [hm.1]
    have : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one h1m
    exact_mod_cast this
  have hU2 : (2 : ℝ) ≤ Real.sqrt X := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX4
  have hb1 := leaf_main_term_bound_exists_C_3 ε (min ε1 ε2) c H0a Ca X0a H X P0 P0 Sg' hHA
    hlow le_rfl hSg m hmX hmpos
  have hb2 := hC'.2 H X P0 P0 (Real.sqrt X) Sg' m hHB hP01 le_rfl hFin hSg hm.1 hm.2 hU2
  exact le_trans (norm_sub_le_norm_sub_add_norm_sub _ _ _) (add_le_add hb1 hb2)

end LeanLab.Pintz2021.DecompJ834
