import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear
import three_qubits.one_qubit
import three_qubits.reg
import three_qubits.CF_rise

macro "unfoldTensorPrSum":tactic =>
`(tactic|(
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul]
))

-- Just a helper lemma. It allows to divide an arbitrary case into:
-- n=1
-- n=2
-- n=3
-- other
lemma help(n:ℕ)(A:Prop):
((n=1)→A) →
((n=2)→A) →
((n=3)→A) →
(¬(n=1)→¬(n=2)→¬(n=3)→A) →
A := by
  intro c1 c2 c3 cn
  cases n
  case zero=>aesop
  case succ m => cases m
                 case zero => aesop
                 case succ k => cases k
                                case zero => aesop
                                case succ r => cases r
                                               case zero => aesop
                                               case succ f => aesop

noncomputable
def repl1(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
         (x y z: Coup R)(p:ℕ):
         Coup R →ₗ[R] triple R :=
{
  toFun(c:Coup R) :=
    if p=1 then pureTriple R c y z else
    if p=2 then pureTriple R x c z else
    if p=3 then pureTriple R x y c else
    0
  map_add' := by
    intro a b
    apply help p
    all_goals intro eq
    all_goals simp [eq]
    all_goals simp [pureTriple, pureDoub]
    all_goals unfoldTensorPrSum
    intro eq2 eq3
    simp [eq, eq2, eq3]
  map_smul' := by
    intro a b
    apply help p
    all_goals intro eq
    all_goals simp [eq]
    all_goals simp [pureTriple, pureDoub]
    rw [TensorProduct.smul_tmul]
    rw [TensorProduct.tmul_smul]
    rw [TensorProduct.smul_tmul]
    rw [TensorProduct.tmul_smul]
    rw [TensorProduct.smul_tmul]
    rw [TensorProduct.tmul_smul]
    intro eq2 eq3
    simp [eq,eq2,eq3]
}

noncomputable
def repl2(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
         (x y z: Coup R)(p1 p2:ℕ)(neq: ¬(p1=p2)):
         Coup R →ₗ[R] (Coup R →ₗ[R] triple R) :=
{
  toFun(c:Coup R) :=
    if p1=1 then repl1 R c y z p2 else
    if p1=2 then repl1 R x c z p2 else
    if p1=3 then repl1 R x y c p2 else
    0
  map_add' := by
    intro a b
    apply help p1
    all_goals intro eq
    all_goals simp [eq]
    {
      simp [repl1]
      apply help p2
      {
        intro eq2
        apply False.elim
        clear a b x y z
        aesop
      }
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr1 R a b c z]
      }
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr1 R a b y c]
      }
      {
        intro e1 e2 e3
        simp [e1, e2, e3]
        ext
        simp
      }
    }
    {
      simp [repl1]
      apply help p2
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr2 R c a b z]
      }
      {
        intro eq2
        apply False.elim
        clear a b x y z
        aesop
      }
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr2 R x a b c]
      }
      {
        intro e1 e2 e3
        simp [e1, e2, e3]
        ext
        simp
      }
    }
    {
      simp [repl1]
      apply help p2
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr3 R c y a b]
      }
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr3 R x c a b]
      }
      {
        intro eq2
        apply False.elim
        clear a b x y z
        aesop
      }
      {
        intro e1 e2 e3
        simp [e1, e2, e3]
        ext
        simp
      }
    }
    intro e1 e2
    simp [e1, e2]
  map_smul' := by
    intro a b
    apply help p1
    all_goals intro eq
    all_goals simp [eq]
    all_goals simp [repl1, pureTriple, pureDoub]
    all_goals apply help p2
    all_goals intro eq2
    all_goals simp [eq2]
    all_goals try rw [eq, eq2] at neq
    all_goals try aesop
}

-- this function puts given doub into given positions in triple x,y,z
noncomputable
def repl(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
        (x y z: Coup R)(p1 p2:ℕ)(neq: ¬(p1=p2)):doub R →ₗ[R] triple R :=
        TensorProduct.lift (repl2 R x y z p1 p2 neq)
