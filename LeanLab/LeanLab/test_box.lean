import LeanLab.ChenDoubleSieve.Burst9Psi2Panels
open LeanLab.ChenDoubleSieve.Burst9Psi2
open LeanLab.ChenDoubleSieve.Wu04Functional

#eval show IO Unit from do
  let p := tableParams 0
  let lo := fun _ : Fin 4 => 1/p.k2
  let hi := fun _ : Fin 4 => 1/p.k3
  let prodLo := ∏ j : Fin 4, lo j
  let vol := ∏ j : Fin 4, (hi j - lo j)
  let box := 1 / ((prodLo) * lo ⟨2, by omega⟩) * vol
  IO.println s!"box bound = {box}"
  IO.println s!"target = {(18727/250000000 : ℝ)}"
