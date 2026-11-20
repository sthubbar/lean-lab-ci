import LeanLab.ChenDoubleSieve.FunctionalStatements

/-! Obstructions to two proposed certificate routes for Wu 2004 page 26.
The literal domains are D2,16 and Table 1 rows one through three on page 30.
The numeric constants concern D2,9 through D2,17.
The fixed rational moments below are auxiliary lab certificate data.
The arithmetic theorem compares constants. It does not identify any integral.
AI wrote the Lean code. Binary Goldbach is open. -/
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task665
open Wu04Functional

/-- Each of the nine existing uniform certificate constants exceeds its target. -/
theorem uniform_certificate_constants_exceed_targets :
    (42971/500000000 : ℝ) < 2165714472688524862929898808528251575864431463187330499089843518337/19689600140510902116350095640211800855091372864659105598225678336000000 ∧
    (14713151/1000000000 : ℝ) < 19202155203527423659384231508484945125428930237640334726078336591261083/734857852517302051208533586300364155535587901309844537088888921462362500 ∧
    (8347739/1000000000 : ℝ) < 15447704285083063763653746492263661320799/1044263836943294616159848850448182477440000 ∧
    (2294543/500000000 : ℝ) < 12873499195081589004557889318181/1586804982195595154779231452248724 ∧
    (870161/62500000 : ℝ) < 120226154046540718828272111526164913326899878180710968732122565447292512905116693403/4862740402048292220348058455330139105952634633830060734762186711484747776560801600000 ∧
    (9342453/1000000000 : ℝ) < 28115168055807306195501361370824709393345950877/1698121333462368779596680399144727984510051240000 ∧
    (2272569/500000000 : ℝ) < 9839993996114040077656413833130680045727607699/1224531946652053838544588869179773775692214788000 ∧
    (24633499/1000000000 : ℝ) < 28941798099259998389101191177130716898771781/660386651956181116763715344464034059423998000 ∧
    (45791/250000000 : ℝ) < 294949906443190799072644908305145741261503881319455213/1301189114858412866442603928625554195690353299649607008000 := by
  norm_num

/-- The existing row one and row two c4 domains do not contain the row three domain. -/
theorem r2j16_literal_domain_transfer_fails :
    ¬ domain (fun _ : Fin 4 => (100 / 287 : ℝ)) (fun _ : Fin 4 => (5 / 12 : ℝ)) ⊆
        domain (fun _ : Fin 4 => (10 / 29 : ℝ)) (fun _ : Fin 4 => (25 / 61 : ℝ)) ∧
    ¬ domain (fun _ : Fin 4 => (100 / 287 : ℝ)) (fun _ : Fin 4 => (5 / 12 : ℝ)) ⊆
        domain (fun _ : Fin 4 => (25 / 72 : ℝ)) (fun _ : Fin 4 => (100 / 243 : ℝ)) := by
  let x : Fin 4 → ℝ := ![413 / 1000, 414 / 1000, 415 / 1000, 416 / 1000]
  have hm : x ∈ domain (fun _ : Fin 4 => (100 / 287 : ℝ)) (fun _ : Fin 4 => (5 / 12 : ℝ)) := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num [x] at *
    · intro j
      fin_cases j <;> norm_num [x]
  constructor
  · apply Set.not_subset.mpr
    refine ⟨x, hm, ?_⟩
    intro hx
    have hu := (hx.2 (0 : Fin 4)).2
    norm_num [x] at hu
  · apply Set.not_subset.mpr
    refine ⟨x, hm, ?_⟩
    intro hx
    have hu := (hx.2 (0 : Fin 4)).2
    norm_num [x] at hu

end LeanLab.ChenDoubleSieve.Task665
