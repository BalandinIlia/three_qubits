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
import three_qubits.insert

def sel(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
       (x y z: Coup R)(n:ℕ):Coup R :=
if n=1 then x else
if n=2 then y else
if n=3 then z else
0

structure CF2 (R: Type)[CommSemiring R][Ring R][Module R (Coup R)] where
func: Coup R → Coup R → doub R
ps1: ∀a b c: Coup R, func (a+b) c = (func a c) + (func b c)
ps2: ∀a b c: Coup R, func a (b+c) = (func a b) + (func a c)
pm1: ∀m:R, ∀a b: Coup R, func (m • a) b = m • (func a b)
pm2: ∀m:R, ∀a b: Coup R, func a (m • b) = m • (func a b)

lemma distr(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
           (p: doub R)(m1 m2 m3: doub R →ₗ[R] triple R)
           (l: ∀a b: Coup R, m1 (TensorProduct.tmul R a b)=
                             m2 (TensorProduct.tmul R a b)+
                             m3 (TensorProduct.tmul R a b)):
  m1 p = m2 p + m3 p := by
  apply TensorProduct.induction_on (motive := fun g:doub R => m1 g = m2 g + m3 g)
  aesop
  apply l
  intros x y a1 a2
  simp [a1, a2]
  module

lemma distr2(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
            (p: doub R)(m1 m2: doub R →ₗ[R] triple R)
            (l: ∀a b: Coup R, m1 (TensorProduct.tmul R a b)=
                              m2 (TensorProduct.tmul R a b)):
  m1 p = m2 p := by
  apply TensorProduct.induction_on (motive := fun g:doub R => m1 g = m2 g)
  aesop
  apply l
  intros x y a1 a2
  simp [a1, a2]

noncomputable
def transTwo (R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
             (cf2: CF2 R)(p1 p2:ℕ)(neq: ¬(p1=p2)):CF R :=
{
  func := fun x y z:Coup R => repl R x y z p1 p2 neq (cf2.func (sel R x y z p1) (sel R x y z p2))
  ps1:= by
    simp [sel]
    apply help p1
    all_goals intros e1
    all_goals simp [e1]
    {
      apply help p2
      all_goals intro e2
      all_goals simp [e2]
      {
        intro eq2
        apply False.elim
        aesop
      }
      {
        simp [cf2.ps1, cf2.ps2]
        simp [repl, repl2]
      }
      {
        simp [cf2.ps1, cf2.ps2]
        simp [repl, repl2]
      }
      intro e3 e4
      simp [e3, e4]
      simp [cf2.ps1, cf2.ps2]
      simp [repl, repl2]
    }
    {
      apply help p2
      all_goals intro e2
      all_goals simp [e2]
      {
        simp [cf2.ps1, cf2.ps2]
        simp [repl, repl2]
        aesop
      }
      {
        intro eq2
        apply False.elim
        aesop
      }
      {
        intro a b c d
        have eq:∀t y :Coup R,
        (repl R (a + b) c d 2 3 (by aesop))
          (TensorProduct.tmul R t y) =
        (repl R a c d 2 3 (by aesop))
          (TensorProduct.tmul R t y) +
        (repl R b c d 2 3 (by aesop))
          (TensorProduct.tmul R t y) := by
          simp [repl]
          simp [repl2]
          simp [repl1]
          simp [lemTr1]
        apply distr R (cf2.func c d)
        apply eq
      }
      intro e3 e4
      intro a b c d
      simp [e3, e4]
      generalize rt:(cf2.func c 0)=gh
      clear rt
      apply distr R gh
      simp [repl, repl2, repl1,e2,e3,e4]
    }
    {
      apply help p2
      all_goals intro e2
      all_goals simp [e2]
      {
        simp [cf2.ps1, cf2.ps2]
        simp [repl, repl2]
        sorry
      }
      {
        simp [repl, repl2]
        intro a b c d
        apply distr R (cf2.func d c)
        simp [repl, repl2, repl1, e2, lemTr1]
      }
      {
        intro eq2
        apply False.elim
        aesop
      }
      intro e3 e4
      simp [e3, e4]
      intro a b c d
      apply distr R (cf2.func d 0)
      simp [repl, repl2, repl1, e2, e3, e4]
    }
    intro e2 e3
    simp [e1, e2, e3]
    apply help p2
    {
      intro c1
      simp [c1]
      simp [cf2.ps2]
      simp [repl, repl2, e1, e2, e3]
    }
    {
      intro c1
      simp [c1]
      intro a b c d
      apply distr R (cf2.func 0 c)
      simp [repl, repl2, e1, e2, e3]
    }
    {
      intro c1
      simp [c1]
      intro a b c d
      apply distr R (cf2.func 0 d)
      simp [repl, repl2, e1, e2, e3]
    }
    intro c1 c2 c3
    simp [c1, c2, c3]
    intro a b c d
    apply distr R (cf2.func 0 0)
    simp [repl, repl2, e1, e2, e3]
  ps2:= by
    simp [sel]
    apply help p1
    all_goals intros e1
    all_goals simp [e1]
    {
      apply help p2
      all_goals intro e2
      all_goals simp [e2]
      {
        intro eq2
        apply False.elim
        aesop
      }
      {
        simp [cf2.ps1, cf2.ps2]
        intro a b c d
        have eq1:(repl R a (b + c) d 1 2 (by aesop)) (cf2.func a b) =
                 (repl R a b d 1 2 (by aesop)) (cf2.func a b):= by
          apply distr2 R (cf2.func a b)
          simp [repl, repl2, repl1]
        have eq2:(repl R a (b + c) d 1 2 (by aesop)) (cf2.func a c) =
                 (repl R a c d 1 2 (by aesop)) (cf2.func a c):= by
          apply distr2 R (cf2.func a c)
          simp [repl, repl2, repl1]
        simp [eq1, eq2]
      }
      {
        intro a b c d
        apply distr R (cf2.func a d)
        simp [repl, repl2, repl1, lemTr2]
      }
      intro e3 e4
      simp [e3, e4]
      intro a b c d
      apply distr R (cf2.func a 0)
      simp [repl, repl2, repl1, lemTr2, e1, e2, e3, e4]
    }
    {
      apply help p2
      all_goals intro e2
      all_goals simp [e2]
      {
        simp [cf2.ps1, cf2.ps2]
        simp [repl, repl2]
      }
      {
        intro eq2
        apply False.elim
        aesop
      }
      {
        intro a b c d
        simp [cf2.ps1, cf2.ps2]
        have eq1:(repl R a (b + c) d 2 3 (by aesop)) (cf2.func b d) =
                 (repl R a b d 2 3 (by aesop)) (cf2.func b d):= by
          apply distr2 R (cf2.func b d)
          simp [repl, repl2, repl1]
        have eq2:(repl R a (b + c) d 2 3 (by aesop)) (cf2.func c d) =
                 (repl R a c d 2 3 (by aesop)) (cf2.func c d):= by
          apply distr2 R (cf2.func c d)
          simp [repl, repl2, repl1]
        simp [eq1, eq2]
      }
      intro e3 e4
      intro a b c d
      simp [e3, e4]
      simp [cf2.ps1, cf2.ps2]
      have eq1:(repl R a (b + c) d 2 p2 (by aesop)) (cf2.func b 0) =
               (repl R a b d 2 p2 (by aesop)) (cf2.func b 0):= by
        apply distr2 R (cf2.func b 0)
        simp [repl, repl2, repl1]
      have eq2:(repl R a (b + c) d 2 p2 (by aesop)) (cf2.func c 0) =
               (repl R a c d 2 p2 (by aesop)) (cf2.func c 0):= by
        apply distr2 R (cf2.func c 0)
        simp [repl, repl2, repl1]
      simp [eq1, eq2]
    }
    all_goals sorry
  ps3:= by sorry
  pm1:= by sorry
  pm2:= by sorry
  pm3:= by sorry
}
