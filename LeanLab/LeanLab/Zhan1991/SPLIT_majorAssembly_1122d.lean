import LeanLab.Zhan1991.MajorArcSep1122
import LeanLab.Zhan1991.RamanujanSum1122

/-!
P0068 Zhan 1991, page 271, step 2 of SPLIT_major_1122: `MajorAssembly` from `MajorArcApprox`,
split. The per arc error bound from `MajorArcApprox`, the algebra of the main term, the Ramanujan
sum over `a`, `μ(q)³ = μ(q)`, and the counting of at most `L^{2d}` arcs are PROVED here. The joining of
the half arcs at 0 and 1 by periodicity, and the decomposition of `[0, 1] ∩ E₁` into disjoint arcs
by `majorArcs_separated`, are PROVED. No LEAF remains: `majorAssembly_of_approx_split` is PROVED
conditional on its hypothesis `MajorArcApprox`, the cited step 1. burst-20261122, label major-assembly.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open Real
open scoped ArithmeticFunction.Moebius
open MeasureTheory

/-- `e(k) = 1` for an integer `k`, page 270. PROVED. -/
theorem ee_intCast_one (k : ℤ) : ee (k : ℝ) = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * (2 * π * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- Page 270, `S(α)³ e(-Nα)` has period 1. PROVED. -/
theorem majorIntegrand_periodic (N : ℕ) (U α : ℝ) :
    primeSum110 N U (α + 1) ^ 3 * ee (-(N : ℝ) * (α + 1)) =
      primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
  have hS : primeSum110 N U (α + 1) = primeSum110 N U α := by
    unfold primeSum110
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show (p : ℝ) * (α + 1) = (p : ℝ) * α + ((p : ℤ) : ℝ) by push_cast; ring, ee_add110,
      ee_intCast_one, mul_one]
  rw [hS, show -(N : ℝ) * (α + 1) = -(N : ℝ) * α + ((-(N : ℤ) : ℤ) : ℝ) by push_cast; ring,
    ee_add110, ee_intCast_one, mul_one]

/-- Distinct reduced fractions are distinct reals: `a/q = a'/q'` with `(a, q) = (a', q') = 1` forces
`a = a'`, `q = q'`. Page 270. PROVED. -/
theorem reduced_frac_eq (q q' a a' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q') (h : Nat.Coprime a q)
    (h' : Nat.Coprime a' q') (he : (a : ℝ) / q = a' / q') : a = a' ∧ q = q' := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0' : (q' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm : a * q' = a' * q := by
    rw [div_eq_div_iff hq0 hq0'] at he; exact_mod_cast he
  have h1 : q ∣ q' := by
    have : q ∣ q' * a := ⟨a', by rw [mul_comm q' a, hm, mul_comm]⟩
    exact (Nat.Coprime.symm h).dvd_of_dvd_mul_right this
  have h2 : q' ∣ q := by
    have : q' ∣ q * a' := ⟨a, by rw [mul_comm q a', ← hm, mul_comm]⟩
    exact (Nat.Coprime.symm h').dvd_of_dvd_mul_right this
  have hqq := Nat.dvd_antisymm h1 h2
  subst hqq
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) hm, rfl⟩

/-- Pages 270 to 271, the major arcs in `[0, 1]` for large `N`: `[0, 1] ∩ E₁` is the half arcs
`[0, w]`, `[1 - w, 1]` of `q = 1` and the full arcs `[a/q - w, a/q + w]` for `2 ≤ q ≤ L^d`,
`1 ≤ a < q`, `(a, q) = 1`, using `majorArcs_separated` to keep reduced fractions with `2 ≤ q` more
than `2w` from `0` and `1`. PROVED. -/
theorem arcs_set_eq_proof (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      Set.Icc (0 : ℝ) 1 ∩ majorArcs110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d =
        Set.Icc 0 (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)) ∪ Set.Icc (1 - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))) 1 ∪
          ⋃ i ∈ (Finset.Icc 2 ⌊(Real.log N ^ d)⌋₊).sigma
              (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)),
            Set.Icc ((i.2 : ℝ) / i.1 - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))) ((i.2 : ℝ) / i.1 + (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))) := by
  obtain ⟨N₂, hsep⟩ := majorArcs_separated d c hd hc.le
  refine ⟨max N₂ (Real.exp 1), fun N hN => ?_⟩
  have hN2 : N₂ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN1' : (1 : ℝ) ≤ N := by have := Real.exp_one_gt_d9; linarith
  have hS := hsep N hN2
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX1 : (1 : ℝ) ≤ X := Real.one_le_rpow hL1 hd.le
  have hX1' : ((1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX1
  have hUpos : 0 < U := mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by linarith) _)
  have hw0 : 0 ≤ w := by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) (4 : ℝ); positivity
  have hw1 : 2 * w < 1 := by
    have := hS 1 1 0 1 le_rfl hX1' le_rfl hX1' (by norm_num)
    norm_num at this; linarith
  -- a reduced fraction `a/q` with `2 ≤ q` is more than `2w` from `0` and from `1`
  have hfar : ∀ (q : ℕ) (a : ℤ), 2 ≤ q → (q : ℝ) ≤ X → Int.gcd a q = 1 →
      2 * w < |(a : ℝ) / q| ∧ 2 * w < |(a : ℝ) / q - 1| := by
    intro q a hq hqX hg
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [Int.gcd_zero_left] at hg; simp at hg; omega
    have haq : a ≠ q := by
      rintro rfl; rw [Int.gcd_self] at hg; simp at hg; omega
    constructor
    · have := hS q 1 a 0 (by omega) hqX le_rfl hX1' (by
        simp only [Int.cast_zero, zero_div, Nat.cast_one]
        exact div_ne_zero (by exact_mod_cast ha0) hq0)
      simpa using this
    · have := hS q 1 a 1 (by omega) hqX le_rfl hX1' (by
        simp only [Int.cast_one, Nat.cast_one, div_one]
        rw [Ne, div_eq_one_iff_eq hq0]
        exact_mod_cast haq)
      simpa using this
  ext α
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion, Set.mem_Icc, majorArcs110,
    Set.mem_ofPred_eq, exists_prop, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨h0, h1⟩, q, hq1, hqX, a, hg, hdist⟩
    rw [abs_le] at hdist
    rcases Nat.lt_or_ge q 2 with hq | hq
    · have hq1' : q = 1 := by omega
      subst hq1'
      simp only [Nat.cast_one, div_one] at hdist
      have ha1 : a ≤ 1 := by
        have : (a : ℝ) < 2 := by linarith [hdist.1]
        exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
      have ha0 : 0 ≤ a := by
        have : (-1 : ℝ) < a := by linarith [hdist.2]
        have : (-1 : ℤ) < a := by exact_mod_cast this
        omega
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · left; left; push_cast at hdist; constructor <;> linarith [hdist.1, hdist.2]
      · left; right; push_cast at hdist; constructor <;> linarith [hdist.1, hdist.2]
    · right
      obtain ⟨hf0, hf1⟩ := hfar q a hq hqX hg
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hlo : 0 < (a : ℝ) / q := by
        by_contra hneg
        push Not at hneg
        rw [abs_of_nonpos hneg] at hf0
        linarith [hdist.1, hdist.2]
      have hhi : (a : ℝ) / q < 1 := by
        by_contra hneg
        push Not at hneg
        rw [abs_of_nonneg (by linarith)] at hf1
        linarith [hdist.1, hdist.2]
      have ha0 : 0 < a := by
        have : (0 : ℝ) < a := by
          have := mul_pos hlo hq0; rwa [div_mul_cancel₀ _ hq0.ne'] at this
        exact_mod_cast this
      have haq : a < q := by
        have : (a : ℝ) < q := by
          have := (div_lt_one hq0).mp hhi; exact this
        exact_mod_cast this
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha0.le
      refine ⟨⟨q, n⟩, ⟨⟨hq, Nat.le_floor hqX⟩, (show n < q by omega), ?_⟩, ?_⟩
      · rw [Int.gcd_natCast_natCast] at hg; exact hg
      · simp only [Int.cast_natCast] at hdist
        constructor <;> linarith [hdist.1, hdist.2]
  · rintro ((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨i, ⟨⟨hi2, hin⟩, hlt, hcop⟩, h0, h1⟩)
    · refine ⟨⟨h0, by linarith⟩, 1, le_rfl, hX1', 0, by norm_num, ?_⟩
      simp only [Int.cast_zero, zero_div, sub_zero]
      rw [abs_le]; constructor <;> linarith
    · refine ⟨⟨by linarith, h1⟩, 1, le_rfl, hX1', 1, by norm_num, ?_⟩
      simp only [Int.cast_one, Nat.cast_one, div_one]
      rw [abs_le]; constructor <;> linarith
    · have hiX : (i.1 : ℝ) ≤ X := (Nat.cast_le.mpr hin).trans (Nat.floor_le (by linarith))
      have hg : Int.gcd (i.2 : ℤ) i.1 = 1 := by rw [Int.gcd_natCast_natCast]; exact hcop
      obtain ⟨hf0, hf1⟩ := hfar i.1 (i.2 : ℤ) hi2 hiX hg
      simp only [Int.cast_natCast] at hf0 hf1
      have hq0 : (0 : ℝ) < i.1 := by exact_mod_cast (by omega : 0 < i.1)
      have hlo : 0 ≤ (i.2 : ℝ) / i.1 := by positivity
      have hhi : (i.2 : ℝ) / i.1 ≤ 1 := (div_le_one hq0).mpr (by exact_mod_cast hlt.le)
      rw [abs_of_nonneg hlo] at hf0
      rw [abs_of_nonpos (by linarith)] at hf1
      refine ⟨⟨by linarith, by linarith⟩, i.1, by omega, hiX, (i.2 : ℤ), hg, ?_⟩
      simp only [Int.cast_natCast]
      rw [abs_le]; constructor <;> linarith

/-- Pages 270 to 271, step 2 of the standard method: the major arc integral over `[0, 1]` is the
sum of the integrals over the disjoint arcs, by `arcs_set_eq_proof`, `majorArcs_separated` and
`reduced_frac_eq`. PROVED. -/
theorem arc_sets_proof (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d =
        ((∫ α in (0 : ℝ)..(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)),
            primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α ^ 3 * ee (-(N : ℝ) * α)) +
          (∫ α in (1 - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..1,
            primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α ^ 3 * ee (-(N : ℝ) * α)) +
          ∑ q ∈ Finset.Icc 2 ⌊(Real.log N ^ d)⌋₊,
            ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              ∫ α in ((a : ℝ) / q - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..((a : ℝ) / q + (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))),
                primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α ^ 3 *
                  ee (-(N : ℝ) * α)).re := by
  obtain ⟨N₁, hset⟩ := arcs_set_eq_proof d c hd hc
  obtain ⟨N₂, hsep⟩ := majorArcs_separated d c hd hc.le
  refine ⟨max (max N₁ N₂) (Real.exp 1), fun N hN => ?_⟩
  have hN1 : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN1' : (1 : ℝ) ≤ N := by have := Real.exp_one_gt_d9; linarith
  have hS := hsep N hN2
  have hE := hset N hN1
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX1 : (1 : ℝ) ≤ X := Real.one_le_rpow hL1 hd.le
  have hUpos : 0 < U := mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by linarith) _)
  have hw0 : 0 ≤ w := by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) (4 : ℝ); positivity
  -- separation in natural number form
  have hSn : ∀ q q' a a' : ℕ, 1 ≤ q → (q : ℝ) ≤ X → 1 ≤ q' → (q' : ℝ) ≤ X →
      (a : ℝ) / q ≠ (a' : ℝ) / q' → 2 * w < |(a : ℝ) / q - (a' : ℝ) / q'| := by
    intro q q' a a' h1 h2 h3 h4 hne
    have := hS q q' (a : ℤ) (a' : ℤ) h1 h2 h3 h4 (by simpa only [Int.cast_natCast] using hne)
    simpa only [Int.cast_natCast] using this
  have hdisjR : ∀ x y : ℝ, 2 * w < |x - y| →
      Disjoint (Set.Icc (x - w) (x + w)) (Set.Icc (y - w) (y + w)) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro z hz hz'
    have : |x - y| ≤ 2 * w := abs_le.mpr ⟨by linarith [hz.1, hz'.2, hz.2, hz'.1], by linarith [hz.2, hz'.1, hz.1, hz'.2]⟩
    linarith
  set I := (Finset.Icc 2 ⌊X⌋₊).sigma
    (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)) with hI
  have hmemI : ∀ i ∈ I, 2 ≤ i.1 ∧ (i.1 : ℝ) ≤ X ∧ 1 ≤ i.2 ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    intro i hi
    rw [hI, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨h2, hn⟩, hlt, hcop⟩ := hi
    refine ⟨h2, (Nat.cast_le.mpr hn).trans (Nat.floor_le (by linarith)), ?_, hlt, hcop⟩
    rcases Nat.eq_zero_or_pos i.2 with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop; omega
    · exact h0
  have hpos : ∀ i ∈ I, 0 < (i.2 : ℝ) / i.1 ∧ (i.2 : ℝ) / i.1 < 1 := by
    intro i hi
    obtain ⟨h2, -, h1, hlt, -⟩ := hmemI i hi
    have hq : (0 : ℝ) < i.1 := by exact_mod_cast (by omega : 0 < i.1)
    refine ⟨div_pos (by exact_mod_cast h1) hq, (div_lt_one hq).mpr (by exact_mod_cast hlt)⟩
  have hA : Set.Icc (0 : ℝ) w ⊆ Set.Icc (((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - w)
      (((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) + w) := by
    intro z hz; simp only [Nat.cast_zero, Nat.cast_one, zero_div, zero_sub, zero_add,
      Set.mem_Icc] at hz ⊢; constructor <;> linarith [hz.1, hz.2]
  have hB : Set.Icc (1 - w) 1 ⊆ Set.Icc (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - w)
      (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) + w) := by
    intro z hz; simp only [Nat.cast_one, div_one, Set.mem_Icc] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  have hAB : Disjoint (Set.Icc (0 : ℝ) w) (Set.Icc (1 - w) 1) :=
    (hdisjR _ _ (hSn 1 1 0 1 le_rfl (by exact_mod_cast hX1) le_rfl (by exact_mod_cast hX1)
      (by norm_num))).mono hA hB
  have hAC : ∀ i ∈ I, Disjoint (Set.Icc (0 : ℝ) w)
      (Set.Icc ((i.2 : ℝ) / i.1 - w) ((i.2 : ℝ) / i.1 + w)) := by
    intro i hi
    obtain ⟨h2, hX, -, -, -⟩ := hmemI i hi
    have := (hpos i hi).1
    exact (hdisjR _ _ (hSn 1 i.1 0 i.2 le_rfl (by exact_mod_cast hX1) (by omega) hX
      (by simp only [Nat.cast_zero, zero_div]; exact this.ne))).mono hA le_rfl
  have hBC : ∀ i ∈ I, Disjoint (Set.Icc (1 - w) 1)
      (Set.Icc ((i.2 : ℝ) / i.1 - w) ((i.2 : ℝ) / i.1 + w)) := by
    intro i hi
    obtain ⟨h2, hX, -, -, -⟩ := hmemI i hi
    have := (hpos i hi).2
    exact (hdisjR _ _ (hSn 1 i.1 1 i.2 le_rfl (by exact_mod_cast hX1) (by omega) hX
      (by simp only [Nat.cast_one, div_one]; exact this.ne'))).mono hB le_rfl
  have hCC : Set.Pairwise (I : Set (Σ _ : ℕ, ℕ)) (Function.onFun Disjoint
      fun i : (Σ _ : ℕ, ℕ) => Set.Icc ((i.2 : ℝ) / i.1 - w) ((i.2 : ℝ) / i.1 + w)) := by
    intro i hi j hj hij
    obtain ⟨hi2, hiX, -, -, hic⟩ := hmemI i hi
    obtain ⟨hj2, hjX, -, -, hjc⟩ := hmemI j hj
    refine hdisjR _ _ (hSn i.1 j.1 i.2 j.2 (by omega) hiX (by omega) hjX ?_)
    intro heq
    obtain ⟨h1, h2⟩ := reduced_frac_eq i.1 j.1 i.2 j.2 (by omega) (by omega) hic hjc heq
    apply hij
    obtain ⟨q, a⟩ := i
    obtain ⟨q', a'⟩ := j
    simp only at h1 h2
    subst h1 h2
    rfl
  have hgc : Continuous fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    have := primeSum_continuous110 N U
    unfold ee; fun_prop
  have hIcc : ∀ x y : ℝ, x ≤ y → (∫ α in Set.Icc x y, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) =
      ∫ α in x..y, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    intro x y h
    rw [intervalIntegral.integral_of_le h, MeasureTheory.integral_Icc_eq_integral_Ioc]
  show (∫ α in Set.Icc (0 : ℝ) 1 ∩ majorArcs110 N U d,
      primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)).re = _
  rw [hE, MeasureTheory.setIntegral_union
      (Set.disjoint_union_left.mpr ⟨Set.disjoint_iUnion₂_right.mpr hAC,
        Set.disjoint_iUnion₂_right.mpr hBC⟩)
      (Finset.measurableSet_biUnion I (fun i _ => measurableSet_Icc))
      ((hgc.integrableOn_Icc).union (hgc.integrableOn_Icc))
      ((MeasureTheory.integrableOn_finset_iUnion).mpr fun i _ => hgc.integrableOn_Icc),
    MeasureTheory.setIntegral_union hAB measurableSet_Icc hgc.integrableOn_Icc
      hgc.integrableOn_Icc,
    MeasureTheory.integral_biUnion_finset I (fun i _ => measurableSet_Icc) hCC
      (fun i _ => hgc.integrableOn_Icc),
    Finset.sum_sigma, hIcc 0 w hw0, hIcc (1 - w) 1 (by linarith)]
  congr 2
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  exact hIcc _ _ (by linarith)

/-- Page 271, the arc decomposition in the shifted form `α = a/q + λ`, `|λ| ≤ w`, PROVED from
`arc_sets_proof`: the two half arcs at `0` and `1` join into `[-w, w]` by periodicity. -/
theorem arc_decomposition_proof (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d =
        (∑ q ∈ Finset.Icc 1 ⌊Real.log N ^ d⌋₊,
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∫ lam in (-(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..
              (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)),
              primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ((a : ℝ) / q + lam) ^ 3 *
                ee (-(N : ℝ) * ((a : ℝ) / q + lam))).re := by
  obtain ⟨N₁, h⟩ := arc_sets_proof d c hd hc
  refine ⟨max N₁ (Real.exp 1), fun N hN => ?_⟩
  rw [h N ((le_max_left _ _).trans hN)]
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by
    push_cast; exact Real.one_le_rpow hL1 hd.le)
  have hgc : Continuous fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    have := primeSum_continuous110 N U
    unfold ee; fun_prop
  have hshift : ∀ (q a : ℕ), (∫ lam in (-w)..w,
      primeSum110 N U ((a : ℝ) / q + lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam))) =
      ∫ α in ((a : ℝ) / q - w)..((a : ℝ) / q + w),
        primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    intro q a
    have := intervalIntegral.integral_comp_add_left
      (fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) ((a : ℝ) / q) (a := -w) (b := w)
    beta_reduce at this
    rw [this, ← sub_eq_add_neg]
  rw [Finset.Icc_eq_cons_Ioc hX1, Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  simp_rw [hshift]
  have hone : (∑ a ∈ (Finset.range 1).filter (fun a => Nat.Coprime a 1),
      ∫ α in ((a : ℝ) / (1 : ℕ) - w)..((a : ℝ) / (1 : ℕ) + w),
        primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) =
      ∫ α in (-w)..w, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    simp
  rw [hone, ← intervalIntegral.integral_add_adjacent_intervals (a := -w) (b := 0) (c := w)
    (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
  have hper : (∫ α in (-w)..0, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) =
      ∫ α in (1 - w)..1, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    have := intervalIntegral.integral_comp_add_right
      (fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) (1 : ℝ) (a := -w) (b := 0)
    beta_reduce at this
    simp_rw [majorIntegrand_periodic] at this
    rw [this]
    congr 1 <;> ring
  rw [hper]
  congr 1
  simp only [Nat.reduceAdd]
  ring

/-- The window `[N/3 - U, N/3 + U]` holds at most `2U + 1` integers, page 271. PROVED. -/
theorem card_Icc_window_le (N : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ((Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊).card : ℝ) ≤ 2 * U + 1 := by
  rw [Nat.card_Icc]
  have hb : 0 ≤ (N : ℝ) / 3 + U := by positivity
  rcases Nat.eq_zero_or_pos (⌊(N : ℝ) / 3 + U⌋₊ + 1 - ⌈(N : ℝ) / 3 - U⌉₊) with h0 | hpos
  · rw [h0]; push_cast; linarith
  · have hle : ⌈(N : ℝ) / 3 - U⌉₊ ≤ ⌊(N : ℝ) / 3 + U⌋₊ + 1 := by omega
    rw [Nat.cast_sub hle]
    push_cast
    have h1 := Nat.floor_le hb
    have h2 := Nat.le_ceil ((N : ℝ) / 3 - U)
    linarith

/-- Page 271, `|S(α)| ≤ 2U + 1`, the trivial bound. PROVED. -/
theorem primeSum_norm_le (N : ℕ) (U α : ℝ) (hU : 0 ≤ U) :
    ‖primeSum110 N U α‖ ≤ 2 * U + 1 := by
  unfold primeSum110
  refine (norm_sum_le _ _).trans ?_
  simp only [ee_norm110, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine le_trans ?_ (card_Icc_window_le N U hU)
  unfold Win
  exact_mod_cast Finset.card_filter_le _ _

/-- Page 271, `|v(λ)| ≤ 2(2U + 1)`, since `1/log n ≤ 2` for `n ≥ 2`, and Lean's `log 0 = log 1 = 0`
makes those terms `0`. PROVED. -/
theorem vSum_norm_le (N : ℕ) (U lam : ℝ) (hU : 0 ≤ U) :
    ‖vSum N U lam‖ ≤ 2 * (2 * U + 1) := by
  unfold vSum
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ‖ee ((n : ℝ) * lam) / (Real.log n : ℂ)‖ ≤ 2 := by
    intro n _
    rw [norm_div, ee_norm110, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have hl : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast h)
      have := Real.log_two_gt_d9
      rw [abs_of_pos (by linarith), div_le_iff₀ (by linarith)]
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have := card_Icc_window_le N U hU
  linarith

/-- `|x³ - y³| ≤ 3 M² |x - y|` for `|x|, |y| ≤ M`, page 271. PROVED. -/
theorem cube_diff_norm (x y : ℂ) (M : ℝ) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖x ^ 3 - y ^ 3‖ ≤ 3 * M ^ 2 * ‖x - y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hx
  have he : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [he, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_add₃_le).trans ?_
  rw [norm_pow, norm_mul, norm_pow]
  have h0 := norm_nonneg x
  have h1 := norm_nonneg y
  nlinarith [mul_le_mul hx hy h1 hM]

/-- `|μ(q)/φ(q)| ≤ 1`, page 271. PROVED. -/
theorem moebius_div_norm_le (q : ℕ) (hq : 1 ≤ q) :
    ‖(((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ))‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hφ : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [abs_of_pos (a := (Nat.totient q : ℝ)) (by linarith), div_le_one (by linarith)]
  have : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  linarith

/-- Page 271, step 2 of the standard method, the error on one arc, PROVED from `MajorArcApprox`
at `A = 2d + 8`: `|S³ - (μ(q)/φ(q) v)³| ≤ 3 M² |S - μ(q)/φ(q) v|` with `M = 2(2U + 1) ≤ 6U`,
over an interval of length `2 L⁴/U`, giving `216 |K| U² L^{-4} / L^{2d}` per arc. -/
theorem arc_error_proof (h1 : MajorArcApprox) (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ K N₀ : ℝ, 0 ≤ K ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (q a : ℕ), 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ d → Nat.Coprime a q →
      ‖∫ lam in (-(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..
            (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)),
          (primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) *
              vSum N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam) ^ 3) *
            ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖
        ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ) /
            (Real.log N ^ d) ^ 2 := by
  obtain ⟨K0, N0, hK0⟩ := h1 d c (2 * d + 8) hd hc (by linarith)
  refine ⟨216 * |K0|, max N0 (Real.exp 1), by positivity, fun N hN q a hq hqX hcop => ?_⟩
  have hN0 : N0 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN1 : (1 : ℝ) ≤ N := by have := Real.exp_one_gt_d9; linarith
  have hLpos : 0 < Real.log N := by linarith
  have hgcd : Int.gcd (a : ℤ) q = 1 := by rw [Int.gcd_natCast_natCast]; exact hcop
  have hA := fun lam => hK0 N q (a : ℤ) lam hN0 hq hqX hgcd
  simp only [Int.cast_natCast] at hA
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  set P := L ^ (-(2 * d + 8)) with hP
  have hU1 : 1 ≤ U := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1 (by norm_num))
    (Real.one_le_rpow hL1 hc.le)
  have hUpos : 0 < U := by linarith
  have hw0 : 0 ≤ w := by have := Real.rpow_nonneg hLpos.le (4 : ℝ); positivity
  have hP0 : 0 ≤ P := Real.rpow_nonneg hLpos.le _
  set M := 2 * (2 * U + 1) with hM
  have hpt : ∀ lam ∈ Set.uIoc (-w) w,
      ‖(primeSum110 N U ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) *
          ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖ ≤ 3 * M ^ 2 * (|K0| * U * P) := by
    intro lam hlam
    rw [Set.uIoc_of_le (by linarith)] at hlam
    have hl : |lam| ≤ w := abs_le.mpr ⟨le_of_lt hlam.1, hlam.2⟩
    rw [norm_mul, ee_norm110, mul_one]
    have hS : ‖primeSum110 N U ((a : ℝ) / q + lam)‖ ≤ M := by
      have := primeSum_norm_le N U ((a : ℝ) / q + lam) hUpos.le; linarith
    have hv : ‖(((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam)‖ ≤ M := by
      rw [norm_mul]
      have h1' := moebius_div_norm_le q hq
      have h2' := vSum_norm_le N U lam hUpos.le
      calc _ ≤ 1 * M := mul_le_mul h1' h2' (norm_nonneg _) zero_le_one
        _ = M := one_mul _
    refine (cube_diff_norm _ _ M hS hv).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (hA lam hl).trans ?_
    have := le_abs_self K0
    have : 0 ≤ U * P := by positivity
    nlinarith
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
  have hpow : P * L ^ (4 : ℝ) = L ^ (-4 : ℝ) / X ^ 2 := by
    rw [hP, hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_add hLpos,
      div_eq_mul_inv, ← Real.rpow_neg hLpos.le, ← Real.rpow_add hLpos]
    congr 1; push_cast; ring
  have hQ : 0 ≤ L ^ (-4 : ℝ) / X ^ 2 := by
    have := Real.rpow_nonneg hLpos.le (-4 : ℝ); positivity
  have hM2 : M ^ 2 ≤ 36 * U ^ 2 := by nlinarith
  rw [show w - -w = 2 * w by ring, abs_of_nonneg (a := 2 * w) (by linarith)]
  calc 3 * M ^ 2 * (|K0| * U * P) * (2 * w) = 6 * M ^ 2 * |K0| * (P * L ^ (4 : ℝ)) := by
        rw [hw]; field_simp; ring
    _ = 6 * M ^ 2 * |K0| * (L ^ (-4 : ℝ) / X ^ 2) := by rw [hpow]
    _ ≤ 6 * (36 * U ^ 2) * |K0| * (L ^ (-4 : ℝ) / X ^ 2) := by gcongr
    _ = 216 * |K0| * U ^ 2 * L ^ (-4 : ℝ) / X ^ 2 := by ring

/-- `μ(q)³ = μ(q)`, page 271. PROVED. -/
theorem moebius_cube (q : ℕ) : (μ q : ℤ) ^ 3 = μ q := by
  by_cases h : Squarefree q
  · have h2 := ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    calc (μ q : ℤ) ^ 3 = μ q * μ q ^ 2 := by ring
      _ = μ q := by rw [h2, mul_one]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; norm_num

/-- Page 271, the main term on the arcs of one `q`: summing `e(-aN/q)` over `a` gives `c_q(N)`,
and `(μ(q)/φ(q))³ = μ(q)/φ(q)³`. PROVED. -/
theorem arc_main_sum (N q : ℕ) (hq : 1 ≤ q) (U w : ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∫ lam in (-w)..w, (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 *
        ee (-(N : ℝ) * ((a : ℝ) / q + lam))) =
      (((μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N : ℝ) : ℂ) *
        ∫ lam in (-w)..w, vSum N U lam ^ 3 * ee (-(N : ℝ) * lam) := by
  have hpt : ∀ a : ℕ, ∀ lam : ℝ,
      (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 *
        ee (-(N : ℝ) * ((a : ℝ) / q + lam)) =
      (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ)) ^ 3 * ee (-((a : ℝ) * N / q)) *
        (vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)) := by
    intro a lam
    rw [show -(N : ℝ) * ((a : ℝ) / q + lam) = -((a : ℝ) * N / q) + -(N : ℝ) * lam by ring,
      ee_add110]
    ring
  simp_rw [hpt, intervalIntegral.integral_const_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ramanujan_sum_complex q N hq]
  have hr : ((μ q : ℝ) / (Nat.totient q : ℝ)) ^ 3 * ramanujanC q N =
      (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N := by
    rw [div_pow, ← Int.cast_pow, moebius_cube]
  rw [← hr]
  push_cast
  ring

/-- Page 271, step 2, `MajorAssembly` from `MajorArcApprox` PROVED, conditional only on its hypothesis,
the cited step 1. -/
theorem majorAssembly_of_approx_split (h1 : MajorArcApprox) : MajorAssembly := by
  refine ⟨1, one_pos, fun d hd c hc => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd
  obtain ⟨N₁, hdec⟩ := arc_decomposition_proof d c hd0 hc
  obtain ⟨K, N₂, hK0, hK⟩ := arc_error_proof h1 d c hd0 hc
  refine ⟨K, max (max N₁ N₂) 3, fun N _ hN => ?_⟩
  have hN1 : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hK' := hK N hN2
  rw [hdec N hN1]
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hLpos d
  have hcont : ∀ (q a : ℕ), Continuous fun lam : ℝ =>
      primeSum110 N U ((a : ℝ) / q + lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam)) := by
    intro q a
    have h0 : Continuous fun lam : ℝ => primeSum110 N U ((a : ℝ) / q + lam) :=
      (primeSum_continuous110 N U).comp (by fun_prop)
    unfold ee
    fun_prop
  have hcontv : ∀ (q a : ℕ), Continuous fun lam : ℝ =>
      (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam)) := by
    intro q a
    unfold vSum ee
    fun_prop
  have harc : ∀ q ∈ Finset.Icc 1 ⌊X⌋₊, ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      (∫ lam in (-w)..w, primeSum110 N U ((a : ℝ) / q + lam) ^ 3 *
          ee (-(N : ℝ) * ((a : ℝ) / q + lam))) =
        (∫ lam in (-w)..w, (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam))) +
        ∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 - (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) *
          ee (-(N : ℝ) * ((a : ℝ) / q + lam)) := by
    intro q _ a _
    rw [← intervalIntegral.integral_add ((hcontv q a).intervalIntegrable _ _)]
    · congr 1; funext lam; ring
    · have := ((hcont q a).sub (hcontv q a))
      refine (this.congr ?_).intervalIntegrable _ _
      intro lam; simp only [Pi.sub_apply]; ring
  rw [Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (harc q hq))]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun q hq => arc_main_sum N q (Finset.mem_Icc.mp hq).1 U w),
    ← Finset.sum_mul, ← Complex.ofReal_sum, Complex.add_re, Complex.re_ofReal_mul]
  set E := ∑ q ∈ Finset.Icc 1 ⌊X⌋₊, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 - (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) *
        ee (-(N : ℝ) * ((a : ℝ) / q + lam)) with hE
  have hmain : singTrunc N X * singInt N U w =
      (∑ q ∈ Finset.Icc 1 ⌊X⌋₊, (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N) *
        (∫ lam in (-w)..w, vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)).re := rfl
  rw [hmain, add_sub_cancel_left]
  set B := K * U ^ 2 * L ^ (-4 : ℝ) / X ^ 2 with hB
  have hB0 : 0 ≤ B := by
    have := Real.rpow_nonneg hLpos.le (-4 : ℝ); positivity
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX.le
  have hnorm : ‖E‖ ≤ (⌊X⌋₊ : ℝ) * ((⌊X⌋₊ : ℝ) * B) := by
    rw [hE]
    refine (norm_sum_le _ _).trans ?_
    have hq : ∀ q ∈ Finset.Icc 1 ⌊X⌋₊,
        ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) * ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖ ≤
          (⌊X⌋₊ : ℝ) * B := by
      intro q hq
      obtain ⟨hq1, hqX⟩ := Finset.mem_Icc.mp hq
      have hqX' : (q : ℝ) ≤ X := (Nat.cast_le.mpr hqX).trans hfl
      refine (norm_sum_le _ _).trans ?_
      have hle : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) * ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖ ≤ B := by
        intro a ha
        exact hK' q a hq1 hqX' (Finset.mem_filter.mp ha).2
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ ⌊X⌋₊ := by
        have := (Finset.card_filter_le (Finset.range q) (fun a => Nat.Coprime a q))
        rw [Finset.card_range] at this
        exact_mod_cast this.trans hqX
      exact mul_le_mul_of_nonneg_right hc hB0
    refine (Finset.sum_le_sum hq).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    simp
  have hfinal : (⌊X⌋₊ : ℝ) * ((⌊X⌋₊ : ℝ) * B) ≤ K * U ^ 2 * L ^ (-4 : ℝ) := by
    have h0 : (0 : ℝ) ≤ ⌊X⌋₊ := Nat.cast_nonneg _
    calc (⌊X⌋₊ : ℝ) * ((⌊X⌋₊ : ℝ) * B) ≤ X * (X * B) :=
          mul_le_mul hfl (mul_le_mul_of_nonneg_right hfl hB0) (by positivity) hX.le
      _ = K * U ^ 2 * L ^ (-4 : ℝ) := by rw [hB]; field_simp
  exact (Complex.abs_re_le_norm E).trans (hnorm.trans hfinal)

end

end LeanLab.Zhan1991
#print axioms LeanLab.Zhan1991.majorAssembly_of_approx_split
#print axioms LeanLab.Zhan1991.arc_error_proof
