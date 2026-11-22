/-
PREP 2026-11-21, KL-cited splitter. SPLIT of Task628.major_arc_block, BlockInputs628.lean.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, pages 5 to 7, displays 16 to 28.

DECISION. Display 28 is proved IN PLACE on pages 5 to 7 from the hypotheses
(A1.2) and (A2.2) of page 5. Those two hypotheses are a CITATION WALL: page 15
asserts them for the primes and for lambda0 only by "the same methods as
Huxley's result on primes in short intervals", with no proof printed. They are
taken here as the named Props A12Corr and A22Corr, not as open leaves.

The printed (A1.2) and (A2.2) put the character chi on both the weight and the
main term f_j. For a principal character of modulus q above one that form is
false, see LevelExceedingOneFails and Eq33RouteE, Eq33RouteF. The circle method
step of display 25 needs chi on the weight only. A12Corr and A22Corr use that
corrected form. This is a QUESTION about the printed hypotheses, not a finding.

The in place part is cut into the Fourier split of the representation count
into major and minor parts, PROVED here, and seven LEAF lemmas: the four term
identity of display 28, the two bounds of display 22, and the four error bounds of displays
20, 24, 26 and 27. The paper keeps eta arbitrary; the leaves fix eta = 1/4,
so every error is at most C Y^(1/2) P^(-1/4), a consequence of the printed bounds.
The final theorem major_arc_block_of_char_inputs proves the exact statement of
Task628.major_arc_block from the leaves, CONDITIONAL ON A12Corr and A22Corr.
For epsilon above 7/18 the block range is empty and nothing is used.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628
import LeanLab.KumchevLiu2007.QuadraticEnergy674

namespace LeanLab.KumchevLiu2007.Prep1121KLMajor

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 5, the function T1 after hypothesis (A2.2), with the weight
f1(u) = 1/log u of page 15 on the interval I1 of page 2 display 5. -/
noncomputable def T1 (X Y β : ℝ) : ℂ :=
  ∑ m ∈ primeWindow X Y, ((1 / Real.log (m : ℝ) : ℝ) : ℂ) *
    fourier (m : ℤ) (β : AddCircle (1 : ℝ))

/-- P0088 page 5, the function T2 after hypothesis (A2.2), with the weight
f2 of page 15 and z0 = Y^(1/4) P^(-2) of page 8 display 34. -/
noncomputable def T2 (Y P β : ℝ) : ℂ :=
  ∑ m ∈ squareWindow Y, ((f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ) *
    fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))

/-- P0088 page 4 display 15. The pairs q, a with q at most P, a from 0 to q and
a coprime to q, which index the major arcs meeting the period interval. -/
noncomputable def arcPairs (P : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ⌊P⌋₊) ×ˢ Finset.range (⌊P⌋₊ + 1)).filter
    (fun v => v.2 ≤ v.1 ∧ Nat.Coprime v.2 v.1)

/-- P0088 page 4 display 15, the closed arc M(q, a) of width R^(-1) in q alpha. -/
def arc (R : ℝ) (v : ℕ × ℕ) : Set ℝ := {α | |(v.1 : ℝ) * α - v.2| ≤ R⁻¹}

/-- P0088 page 5, S1* on M: mu(q)/phi(q) T1(alpha - a/q) on M(q, a), Q = H/P. -/
noncomputable def S1star (X Y H P α : ℝ) : ℂ :=
  ∑ v ∈ arcPairs P, (arc (H / P) v).indicator
    (fun α => ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
      T1 X Y (α - v.2 / v.1)) α

/-- P0088 page 5, S2* on M: S(q, a)/phi(q) T2(alpha - a/q) on M(q, a), with S(q, a)
of page 3 display 8. -/
noncomputable def S2star (Y H P α : ℝ) : ℂ :=
  ∑ v ∈ arcPairs P, (arc (H / P) v).indicator
    (fun α => U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) *
      T2 Y P (α - v.2 / v.1)) α

/-- P0088 page 7 display 28, left side: the integral of S1 S2 e(-alpha n) over the
major arcs M in one period. -/
noncomputable def majorIntegral (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (primeSum X Y α * roughSum Y P α)

/-- P0088 page 7 display 28, first term: S1* S2* over M0, where M0 of display 23
has width 1/(q Q0), Q0 = Y P^(-3) of display 14, written as majorArcs (Y P^(-2)) P. -/
noncomputable def termA (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (S1star X Y H P α * S2star Y H P α)

/-- P0088 page 7 display 28, second term, bounded in display 20. -/
noncomputable def termB (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      (primeSum X Y α * (roughSum Y P α - S2star Y H P α))

/-- P0088 page 7 display 28, third term over m0 = M minus M0, bounded in display 24. -/
noncomputable def termC (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P),
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (primeSum X Y α * S2star Y H P α)

/-- P0088 page 7 display 28, fourth term over M0, bounded in display 26. -/
noncomputable def termD (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      ((primeSum X Y α - S1star X Y H P α) * S2star Y H P α)

/-- P0088 page 7 display 28 error size O(Y^(1/2) P^(-1/2 + eta)) with eta = 1/4, in
the block range of Task628.major_arc_block and the window Y = X^(7/12 + eps/2) of
page 16. The range is empty for eps above 7/18. -/
def BlockErrorBound (E : ℝ → ℝ → ℝ → ℝ → ℕ → ℂ) : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      ∀ n : ℕ, ‖E X (windowY X ε) H (Real.log X ^ B) n‖ ≤
        C * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-(1 / 4 : ℝ))

/-- P0088 page 5 hypothesis (A1.2) for the primes, defect with chi on the weight
only, the form the character expansion of display 25 uses. -/
noncomputable def primeDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (X Y u v : ℝ) : ℂ :=
  ∑ m ∈ (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
    ((if m.Prime then χ m else 0) -
      (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0))

/-- CITED, NAMED HYPOTHESIS. P0088 page 5 (A1.2) for lambda1 the primes, as asserted on
page 15 by the methods of Huxley's theorem, with chi on the weight only. -/
def A12Corr : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖primeDefect χ X (windowY X ε) u v‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)

/-- P0088 page 5 hypothesis (A2.2) for lambda2 = lambda0 of display 34, defect with chi
on the weight only. -/
noncomputable def roughDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (Y P δ t : ℝ) : ℂ :=
  ∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t),
    (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
      (if χ = 1 then ((f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
       else 0))

/-- CITED, NAMED HYPOTHESIS. P0088 page 5 (A2.2) for lambda0 with the f2 of page 15,
asserted there by the same Huxley type methods, with chi on the weight only,
for 0 < delta at most q Q / Y, Q = H/P of display 14. -/
def A22Corr : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 * (Real.log X ^ B) ^ (-4 : ℤ)

/-- P0088 page 6 display 22 for j = 1, all |beta| at most 1/2. -/
def T1BoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
    ∀ β : ℝ, |β| ≤ 1 / 2 →
      ‖T1 X (windowY X ε) β‖ ≤ C * windowY X ε / (1 + windowY X ε * |β|)

/-- P0088 page 6 display 22 for j = 2, only for |beta| at most Y^(-1/2)/4, where the
phase derivative is at most 1/2. For larger beta display 22 fails for T2: near
beta = 1/3 the sum has no cancellation. QUESTION Q2 of the step notes. -/
def T2BoundProp : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
    ∀ β : ℝ, |β| ≤ 1 / (4 * Real.sqrt (windowY X ε)) →
      ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤
        C * Real.sqrt (windowY X ε) / (1 + windowY X ε * |β|)

/-- PROVED. P0088 page 4 display 13 split at display 15. The representation count is the
major arc integral plus the minor arc Fourier coefficient, by
representationPolynomial_fourierCoeff, fourierCoeff_eq_intervalIntegral and
representationPolynomial_eq_prime_mul_rough. -/
theorem roughCount_eq_major_add_minor (X Y H P : ℝ) (n : ℕ) :
    (roughCount X Y P n : ℂ) = majorIntegral X Y H P n + minorCoefficient X Y H P n := by
  have hcont : Continuous (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      representationPolynomial X Y P (α : AddCircle (1 : ℝ))) := by
    have hc : Continuous (fun α : ℝ => (α : AddCircle (1 : ℝ))) := AddCircle.continuous_mk' 1
    refine ((fourier _).continuous.comp hc).mul ?_
    unfold representationPolynomial
    exact continuous_finsetSum _ (fun v _ => (fourier _).continuous.comp hc)
  have hint : IntegrableOn (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      representationPolynomial X Y P (α : AddCircle (1 : ℝ))) (Set.Ioc 0 1) :=
    hcont.integrableOn_Ioc
  rw [← representationPolynomial_fourierCoeff X Y P n,
    fourierCoeff_eq_intervalIntegral _ _ 0, zero_add,
    intervalIntegral.integral_of_le zero_le_one, div_one, one_smul]
  simp_rw [smul_eq_mul]
  rw [← integral_inter_add_sdiff (measurableSet_majorArcs H P) hint, majorIntegral,
    minorCoefficient, Set.sdiff_eq]
  congr 1
  refine setIntegral_congr_fun ((measurableSet_Ioc).inter (measurableSet_majorArcs H P)) ?_
  intro α _
  simp only [representationPolynomial_eq_prime_mul_rough]

/-- Page 5 display 21: every shifted Fourier character is essentially bounded. -/
theorem fourier_shift_memLp_top (k : ℤ) (c : ℝ) :
    MemLp (fun α : ℝ => fourier k ((α - c : ℝ) : AddCircle (1 : ℝ))) ⊤ volume := by
  apply memLp_top_of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun α => by simp [fourier_apply, Circle.norm_coe])

/-- Page 5 display 21: the finite model sum T1 is essentially bounded. -/
theorem T1_memLp_top (X Y c : ℝ) : MemLp (fun α => T1 X Y (α - c)) ⊤ volume := by
  unfold T1
  exact memLp_finsetSum _ (fun m _ => (fourier_shift_memLp_top (m : ℤ) c).const_mul _)

/-- Page 5 display 21: the finite model sum T2 is essentially bounded. -/
theorem T2_memLp_top (Y P c : ℝ) : MemLp (fun α => T2 Y P (α - c)) ⊤ volume := by
  unfold T2
  exact memLp_finsetSum _ (fun m _ => (fourier_shift_memLp_top ((m ^ 2 : ℕ) : ℤ) c).const_mul _)

/-- Page 4 display 15: each closed major arc is measurable. -/
theorem measurableSet_arc (R : ℝ) (v : ℕ × ℕ) : MeasurableSet (arc R v) := by
  unfold arc
  exact measurableSet_le (by fun_prop) measurable_const

/-- Page 5 display 16: the piecewise model S1star is essentially bounded. -/
theorem S1star_memLp_top (X Y H P : ℝ) : MemLp (S1star X Y H P) ⊤ volume := by
  unfold S1star
  exact memLp_finsetSum _ (fun v _ =>
    ((T1_memLp_top X Y (v.2 / v.1)).const_mul _).indicator
      (measurableSet_arc (H / P) v).nullMeasurableSet)

/-- Page 5 display 17: the piecewise model S2star is essentially bounded. -/
theorem S2star_memLp_top (Y H P : ℝ) : MemLp (S2star Y H P) ⊤ volume := by
  unfold S2star
  exact memLp_finsetSum _ (fun v _ =>
    ((T2_memLp_top Y P (v.2 / v.1)).const_mul _).indicator
      (measurableSet_arc (H / P) v).nullMeasurableSet)

/-- Page 4 display 13: the prime sum is essentially bounded. -/
theorem primeSum_memLp_top (X Y : ℝ) : MemLp (primeSum X Y) ⊤ volume := by
  unfold primeSum
  simpa only [sub_zero] using
    memLp_finsetSum ((primeWindow X Y).filter Nat.Prime)
      (fun m _ => fourier_shift_memLp_top (m : ℤ) 0)

/-- Page 4 display 13: the rough sum is essentially bounded. -/
theorem roughSum_memLp_top (Y P : ℝ) : MemLp (roughSum Y P) ⊤ volume := by
  unfold roughSum
  simpa only [sub_zero] using memLp_finsetSum (squareWindow Y)
    (fun m _ => (fourier_shift_memLp_top ((m ^ 2 : ℕ) : ℤ) 0).const_mul
      (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m))

/-- Page 4 display 15: increasing H narrows the major arcs. -/
theorem majorArcs_antitone {H K P : ℝ} (hH : 0 < H) (hP : 0 < P) (hHK : H ≤ K) :
    majorArcs K P ⊆ majorArcs H P := by
  rintro α ⟨q, hq, hqP, a, hcop, hα⟩
  exact ⟨q, hq, hqP, a, hcop, hα.trans
    (inv_anti₀ (div_pos hH hP) (div_le_div_of_nonneg_right hHK hP.le))⟩

/-- LEAF: P0088 page 7 display 28, the four term identity. In the block range M0 lies in
M since Q0 = Y P^(-3) is at least Q = H/P, and every integrand is bounded and
measurable on the period, so the integral splits over M0 and M minus M0. -/
theorem major_decomp :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) → ∀ n : ℕ,
        majorIntegral X (windowY X ε) H (Real.log X ^ B) n =
          termA X (windowY X ε) H (Real.log X ^ B) n +
          termB X (windowY X ε) H (Real.log X ^ B) n +
          termC X (windowY X ε) H (Real.log X ^ B) n +
          termD X (windowY X ε) H (Real.log X ^ B) n := by
  intro B hB ε hε hε'
  refine ⟨3, ?_⟩
  intro X H hX hlo hhi n
  let Y := windowY X ε
  let P := Real.log X ^ B
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hP : 0 < P := by linarith
  have hY : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hH : 0 < H := lt_of_lt_of_le (mul_pos
    (Real.rpow_pos_of_pos hX0 _) (zpow_pos hP _)) hlo
  have hHK : H ≤ Y * P ^ (-2 : ℤ) := hhi.trans
    (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hP1 (by norm_num)) hY.le)
  have hsub : majorArcs (Y * P ^ (-2 : ℤ)) P ⊆ majorArcs H P :=
    majorArcs_antitone hH hP hHK
  let e : ℝ → ℂ := fun α => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))
  let p : ℝ → ℂ := primeSum X Y
  let r : ℝ → ℂ := roughSum Y P
  let s : ℝ → ℂ := S1star X Y H P
  let t : ℝ → ℂ := S2star Y H P
  let M := Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P
  let M0 := Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P
  have he : MemLp e ⊤ volume := by
    simpa only [sub_zero] using fourier_shift_memLp_top (-(n : ℤ)) 0
  have hp : MemLp p ⊤ volume := primeSum_memLp_top X Y
  have hr : MemLp r ⊤ volume := roughSum_memLp_top Y P
  have hs : MemLp s ⊤ volume := S1star_memLp_top X Y H P
  have ht : MemLp t ⊤ volume := S2star_memLp_top Y H P
  have hint (f : ℝ → ℂ) (hf : MemLp f ⊤ volume) (U : Set ℝ)
      (hU : U ⊆ Set.Ioc (0 : ℝ) 1) : IntegrableOn f U := by
    have hper : IntegrableOn f (Set.Ioc (0 : ℝ) 1) :=
      MemLp.integrable (by simp) (hf.mono_measure Measure.restrict_le_self)
    exact hper.mono_set hU
  have hB : IntegrableOn (fun α => e α * (p α * (r α - t α))) M :=
    hint _ (he.mul (r := ⊤) (hp.mul (r := ⊤) (hr.sub ht))) _ Set.inter_subset_left
  have hpt : IntegrableOn (fun α => e α * (p α * t α)) M :=
    hint _ (he.mul (r := ⊤) (hp.mul (r := ⊤) ht)) _ Set.inter_subset_left
  have hst : IntegrableOn (fun α => e α * (s α * t α)) M0 :=
    hint _ (he.mul (r := ⊤) (hs.mul (r := ⊤) ht)) _ Set.inter_subset_left
  have hD : IntegrableOn (fun α => e α * ((p α - s α) * t α)) M0 :=
    hint _ (he.mul (r := ⊤) ((hp.sub hs).mul (r := ⊤) ht)) _ Set.inter_subset_left
  have hsplit := integral_inter_add_sdiff
    (measurableSet_majorArcs (Y * P ^ (-2 : ℤ)) P) hpt
  have hset0 : M ∩ majorArcs (Y * P ^ (-2 : ℤ)) P = M0 := by
    ext α
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, hsub h.2⟩, h.2⟩
  have hsetC : M \ majorArcs (Y * P ^ (-2 : ℤ)) P =
      Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P) := by
    ext α
    simp only [M, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hset0, hsetC] at hsplit
  change (∫ α in M, e α * (p α * r α)) =
    (∫ α in M0, e α * (s α * t α)) +
    (∫ α in M, e α * (p α * (r α - t α))) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P), e α * (p α * t α)) +
    (∫ α in M0, e α * ((p α - s α) * t α))
  have hfirst : (∫ α in M, e α * (p α * r α)) =
      (∫ α in M, e α * (p α * (r α - t α))) +
      (∫ α in M, e α * (p α * t α)) := by
    rw [← integral_add hB hpt]
    congr 1
    ext α
    ring
  have hsecond : (∫ α in M0, e α * (p α * t α)) =
      (∫ α in M0, e α * (s α * t α)) +
      (∫ α in M0, e α * ((p α - s α) * t α)) := by
    rw [← integral_add hst hD]
    congr 1
    ext α
    ring
  rw [hfirst, ← hsplit, hsecond]
  ring

/-- Page 6 display 22 for j equal to one: partial summation gives the
geometric bound on any prime window whose lower endpoint is at least three. -/
theorem T1_geometric_bound {X Y : ℝ} (hlo : 3 ≤ X - Y) (β : ℝ) :
    ‖T1 X Y β‖ ≤ LeanLab.PNTPort.Vinogradov.G ((primeWindow X Y).card : ℝ) β := by
  let L : ℕ := ⌈X - Y⌉₊
  let N : ℕ := ⌈X⌉₊ - L
  let w : ℕ → ℝ := fun j => 1 / Real.log ((L + j : ℕ) : ℝ)
  have hL3 : (3 : ℝ) ≤ L := hlo.trans (Nat.le_ceil _)
  have hLj (j : ℕ) : (3 : ℝ) ≤ (L + j : ℕ) := by
    push_cast
    exact hL3.trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  have hlog (j : ℕ) : 1 ≤ Real.log ((L + j : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith [hLj j])]
    exact Real.exp_one_lt_three.le.trans (hLj j)
  have hw0 (j : ℕ) : 0 ≤ w j := by dsimp [w]; positivity
  have hw : Antitone w := by
    intro i j hij
    apply one_div_le_one_div_of_le
    · linarith [hlog i]
    · apply Real.log_le_log
      · linarith [hLj i]
      · exact_mod_cast Nat.add_le_add_left hij L
  have hgeom := Task674.norm_weighted_linear_phase_le w N (L - 1) β hw hw0
  have hL1 : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ L by linarith)
  have hphase (j : ℕ) :
      LeanLab.PNTPort.LargeSieve.e ((((L - 1 + 1 : ℕ) : ℝ) * β + (j : ℝ) * β)) =
      fourier ((L + j : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
    rw [Task556d.fourier_nat_eq_e, Nat.sub_add_cancel hL1]
    congr 1
    push_cast
    ring
  simp_rw [hphase] at hgeom
  have heq : T1 X Y β = ∑ j ∈ Finset.range N, w j •
      fourier ((L + j : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
    unfold T1
    rw [Task556d.primeWindow_eq_Ico, Finset.sum_Ico_eq_sum_range]
    rfl
  rw [heq]
  have hw1 : w 0 ≤ 1 := by
    dsimp [w]
    exact (one_div_le_one_div_of_le (by norm_num) (hlog 0)).trans (by norm_num)
  have hcard : ((primeWindow X Y).card : ℝ) = (N : ℝ) := by
    rw [Task556d.primeWindow_eq_Ico, Nat.card_Ico]
  rw [hcard]
  exact hgeom.trans (by
    simpa using mul_le_mul_of_nonneg_right hw1
      (LeanLab.PNTPort.Vinogradov.G_nonneg (Nat.cast_nonneg N) β))

/-- Page 6 display 22: distance to the nearest integer is the absolute
value on the centered half period. -/
theorem dist0_eq_abs_of_abs_le_half {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    LeanLab.PNTPort.LargeSieve.dist0 β = |β| := by
  by_cases h : β = 1 / 2
  · subst β
    norm_num [LeanLab.PNTPort.LargeSieve.dist0, round_eq]
  · have hr : round β = 0 := round_eq_zero_iff.mpr
      ⟨(abs_le.mp hβ).1, lt_of_le_of_ne (abs_le.mp hβ).2 h⟩
    simp [LeanLab.PNTPort.LargeSieve.dist0, hr]

/-- Page 6 display 22 for j equal to one on a single prime window.
The geometric bound and the trivial cardinal bound give the stated decay. -/
theorem T1_decay_bound {X Y : ℝ} (hlo : 3 ≤ X - Y) (hY : 1 ≤ Y)
    {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    ‖T1 X Y β‖ ≤ 4 * Y / (1 + Y * |β|) := by
  have hgeom := T1_geometric_bound hlo β
  have hcard := Task556d.primeWindow_card_le (by linarith : 0 ≤ X - Y) hY
  have htriv : ‖T1 X Y β‖ ≤ 2 * Y := hgeom.trans
    ((LeanLab.PNTPort.Vinogradov.G_le _ _).trans hcard)
  have hweight : ‖T1 X Y β‖ * |β| ≤ 1 / 2 := by
    by_cases hz : |β| = 0
    · rw [hz, mul_zero]
      norm_num
    · have hpos : 0 < |β| := lt_of_le_of_ne (abs_nonneg β) (Ne.symm hz)
      have hdist : 0 < LeanLab.PNTPort.LargeSieve.dist0 β := by
        rwa [dist0_eq_abs_of_abs_le_half hβ]
      have h := hgeom.trans (LeanLab.PNTPort.Vinogradov.G_le_inv hdist)
      rw [dist0_eq_abs_of_abs_le_half hβ] at h
      have hmul := (le_div_iff₀ (by positivity : 0 < 2 * |β|)).mp h
      nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 1 + Y * |β|)).mpr
  calc
    ‖T1 X Y β‖ * (1 + Y * |β|) = ‖T1 X Y β‖ + Y * (‖T1 X Y β‖ * |β|) := by ring
    _ ≤ 2 * Y + Y * (1 / 2) := add_le_add htriv
      (mul_le_mul_of_nonneg_left hweight (by linarith))
    _ ≤ 4 * Y := by linarith

/-- LEAF: P0088 page 6 display 22 for j = 1, from display 21 for f1 = 1/log u by
partial summation against the geometric sum bound min(Y, 1/(2|beta|)). -/
theorem T1_bound : T1BoundProp := by
  intro ε hε hε'
  have hθ : 0 < (7 / 12 + ε / 2 : ℝ) := by linarith
  have hθ' : 0 < (1 - (7 / 12 + ε / 2) : ℝ) := by linarith
  have hlarge : ∀ᶠ X : ℝ in Filter.atTop,
      4 ≤ windowY X ε ∧ 2 ≤ X ^ (1 - (7 / 12 + ε / 2)) ∧ 3 ≤ X :=
    ((tendsto_rpow_atTop hθ).eventually_ge_atTop 4).and
      (((tendsto_rpow_atTop hθ').eventually_ge_atTop 2).and
        (Filter.eventually_ge_atTop 3))
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨4, X0, by norm_num, ?_⟩
  intro X hX β hβ
  obtain ⟨hY4, hratio, hX3⟩ := hX0 X hX
  have hX0' : 0 < X := by linarith
  have hXY : X = windowY X ε * X ^ (1 - (7 / 12 + ε / 2)) := by
    rw [windowY, ← Real.rpow_add hX0']
    ring_nf
    rw [Real.rpow_one]
  have hlo : 3 ≤ X - windowY X ε := by nlinarith
  exact T1_decay_bound hlo (by linarith) hβ

/-- LEAF: P0088 page 6 display 22 for j = 2, from display 21 for f2 by partial
summation and the Kuzmin Landau bound, phase derivative 2 beta m at most 1/2. -/
theorem T2_bound : T2BoundProp := by
  sorry

/-- LEAF: P0088 page 7 display 27, with the tail of the completed integral after
display 26. Uses display 22 through the two named bounds; the tail over
|beta| above Y^(-1/2)/4 needs a mean value bound for T2 beyond display 22. -/
theorem bound27 (h1 : T1BoundProp) (h2 : T2BoundProp) :
    BlockErrorBound (fun X Y H P n => termA X Y H P n - series2 n P * (singInt X Y P n : ℂ)) := by
  sorry

/-- LEAF: P0088 page 6 display 20 from displays 16 to 19, Gallagher's lemma with the
Saffari Vaughan device and hypothesis (A2.2), here A22Corr; H at most Y P^(-4)
keeps the delta edge term at most P^(-4). -/
theorem bound20 (h : A22Corr) : BlockErrorBound termB := by
  sorry

/-- LEAF: P0088 page 6 display 24, Cauchy with display 17, the Gauss sum bound
|S(q, a)| at most q^(1/2 + eta) and display 22 for T2 on |beta| between 1/(q Q0)
and 1/(q Q). -/
theorem bound24 (h2 : T2BoundProp) : BlockErrorBound termC := by
  sorry

/-- LEAF: P0088 page 6 display 26 from display 25, partial summation with hypothesis
(A1.2), here A12Corr, and display 22 for T2. -/
theorem bound26 (hA : A12Corr) (h2 : T2BoundProp) : BlockErrorBound termD := by
  sorry

/-- P0088 page 16: for eps above 7/18 the block range of Task628.major_arc_block is empty. -/
theorem block_range_empty {X H B ε : ℝ} (hX : 3 ≤ X) (hε : 7 / 18 < ε)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H)
    (hhi : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) : False := by
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hP : 0 < (Real.log X ^ B) ^ (-4 : ℤ) := zpow_pos (Real.rpow_pos_of_pos hL _) _
  have h := (mul_le_mul_iff_left₀ hP).mp (hlo.trans hhi)
  rw [windowY] at h
  have h2 := (Real.rpow_le_rpow_left_iff hX1).mp h
  linarith

/-- P0088 page 7 display 28 squared: the exact statement of Task628.major_arc_block,
from the seven leaves above and the proved Fourier split. CONDITIONAL ON the cited A12Corr and A22Corr. -/
theorem major_arc_block_of_char_inputs (hA12 : A12Corr) (hA22 : A22Corr)
    (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A := by
  refine ⟨2 * A + 1, by linarith, ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := by linarith
  by_cases hεhi : 7 / 18 < ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX hlo hhi n
    exact (block_range_empty hX hεhi hlo hhi).elim
  have hε' : ε ≤ 7 / 18 := le_of_not_gt hεhi
  obtain ⟨X0, hdec⟩ := major_decomp B hBpos ε hε hε'
  obtain ⟨C1, X1, hC1, h27⟩ := bound27 T1_bound T2_bound B hBpos ε hε hε'
  obtain ⟨C2, X2, hC2, h20⟩ := bound20 hA22 B hBpos ε hε hε'
  obtain ⟨C3, X3, hC3, h24⟩ := bound24 T2_bound B hBpos ε hε hε'
  obtain ⟨C4, X4, hC4, h26⟩ := bound26 hA12 T2_bound B hBpos ε hε hε'
  set K := C1 + C2 + C3 + C4 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K ^ 2, max (max (max X0 X1) (max X2 X3)) (max X4 3), by positivity,
    le_trans (by norm_num) (le_max_right _ _ |>.trans (le_max_right _ _)), ?_⟩
  intro X H hX hlo hhi n
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_left _ _ |>.trans
    (le_max_left _ _))) hX
  have hX1 : X1 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_left _ _ |>.trans
    (le_max_left _ _))) hX
  have hX2 : X2 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _ |>.trans
    (le_max_left _ _))) hX
  have hX3 : X3 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _ |>.trans
    (le_max_left _ _))) hX
  have hX4 : X4 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _)) hX
  have hX5 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _)) hX
  set Y := windowY X ε with hY
  set L := Real.log X with hLdef
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX5
  have hLpos : 0 < L := by linarith
  have hYnn : 0 ≤ Y := Real.rpow_nonneg hXpos.le _
  set E := ‖majorError X Y H (L ^ B) n‖ with hE
  set R := (L ^ B) ^ (-(1 / 4 : ℝ)) with hR
  have hRnn : 0 ≤ R := Real.rpow_nonneg (Real.rpow_nonneg hLpos.le _) _
  have hsplit : majorError X Y H (L ^ B) n =
      (termA X Y H (L ^ B) n - series2 n (L ^ B) * (singInt X Y (L ^ B) n : ℂ)) +
        termB X Y H (L ^ B) n + termC X Y H (L ^ B) n + termD X Y H (L ^ B) n := by
    rw [majorError, roughCount_eq_major_add_minor X Y H (L ^ B) n,
      hdec X H hX0 hlo hhi n]
    ring
  have hbound : E ≤ K * Real.sqrt Y * R := by
    rw [hE, hsplit]
    have a1 := h27 X H hX1 hlo hhi n
    have a2 := h20 X H hX2 hlo hhi n
    have a3 := h24 X H hX3 hlo hhi n
    have a4 := h26 X H hX4 hlo hhi n
    calc _ ≤ ‖termA X Y H (L ^ B) n - series2 n (L ^ B) * (singInt X Y (L ^ B) n : ℂ)‖ +
          ‖termB X Y H (L ^ B) n‖ + ‖termC X Y H (L ^ B) n‖ + ‖termD X Y H (L ^ B) n‖ :=
            norm_add₄_le
      _ ≤ C1 * Real.sqrt Y * R + C2 * Real.sqrt Y * R + C3 * Real.sqrt Y * R +
          C4 * Real.sqrt Y * R := by gcongr
      _ = K * Real.sqrt Y * R := by rw [hK]; ring
  have hRsq : R ^ 2 ≤ L ^ (-A) := by
    have h1 : R = L ^ (B * (-(1 / 4 : ℝ))) := by rw [hR, ← Real.rpow_mul hLpos.le]
    have h2 : R ^ 2 = L ^ (-(B / 2)) := by
      rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
      congr 1
      push_cast
      ring
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hEnn : 0 ≤ E := norm_nonneg _
  calc E ^ 2 ≤ (K * Real.sqrt Y * R) ^ 2 := pow_le_pow_left₀ hEnn hbound 2
    _ = K ^ 2 * Y * R ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hYnn]
    _ ≤ K ^ 2 * Y * L ^ (-A) := by gcongr
    _ = K ^ 2 * Y / L ^ A := by rw [Real.rpow_neg hLpos.le, div_eq_mul_inv]

/-- The theorem above has the exact type of the sealed leaf Task628.major_arc_block. -/
example (hA12 : A12Corr) (hA22 : A22Corr) : type_of% @Task628.major_arc_block :=
  major_arc_block_of_char_inputs hA12 hA22

end LeanLab.KumchevLiu2007.Prep1121KLMajor

#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.major_arc_block_of_char_inputs
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.block_range_empty
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.roughCount_eq_major_add_minor

#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.fourier_shift_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T2_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.measurableSet_arc
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.S1star_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.S2star_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.primeSum_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.roughSum_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.majorArcs_antitone
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_geometric_bound
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.dist0_eq_abs_of_abs_le_half
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_decay_bound
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.major_decomp
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_bound
