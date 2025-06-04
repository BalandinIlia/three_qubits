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

-- FUNCTION PURPOSE
-- This function is a core of the transformation.
-- In fact this function defines transformation of triple instances.
-- However it defines it explicitly only for pure states: c₁⊗c₂⊗c₃.
-- This funcition is later lifted to define transformation for entangled states.
-- CF means core function
structure CF(R: Type)[CommSemiring R][Ring R][Module R (Coup R)] where
func: Coup R → Coup R → Coup R → triple R
ps1: ∀a b c d: Coup R, func (a+b) c d = (func a c d) + (func b c d)
ps2: ∀a b c d: Coup R, func a (b+c) d = (func a b d) + (func a c d)
ps3: ∀a b c d: Coup R, func a b (c+d) = (func a b c) + (func a b d)
pm1: ∀m:R, ∀a b c: Coup R, func (m • a) b c = m • (func a b c)
pm2: ∀m:R, ∀a b c: Coup R, func a (m • b) c = m • (func a b c)
pm3: ∀m:R, ∀a b c: Coup R, func a b (m • c) = m • (func a b c)

-- Here we start transforming core into linear map to linear map...
-- This is the first step: we eliminate the first parameter of core
noncomputable
def coreLin1(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
            (cf: CF R)
            (x y: Coup R):
            Coup R →ₗ[R] triple R :=
{
  toFun(z:Coup R) := cf.func x y z
  map_add' := by
    intro a b
    apply cf.ps3
  map_smul' := by
    intro m a
    rw [cf.pm3]
    simp
}

-- Here we continue transforming core into linea map.
-- Here we eliminate the second parameter of core.
noncomputable
def coreLin2(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
            (cf: CF R)
            (x: Coup R):
            Coup R →ₗ[R] (Coup R →ₗ[R] triple R) :=
{
  toFun(y:Coup R) := coreLin1 R cf x y
  map_add' := by
    intro x1 y1
    ext g
    simp [coreLin1]
    apply cf.ps2
  map_smul' := by
    intro x1 y1
    ext g
    simp [coreLin1]
    apply cf.pm2
}

-- Here we transformed core into linear map
-- However this map is: core + some its properties proven
-- In other words this map still works only with c₁⊗c₂⊗c₃ and can't work with arbitrary triple
noncomputable
def coreLin3(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
            (cf: CF R):
            Coup R →ₗ[R] (
                      Coup R →ₗ[R] (
                                 Coup R →ₗ[R] triple R
                                 )
                      ) :=
{
  toFun(c:Coup R) := coreLin2 R cf c
  map_add' := by
    intro x1 y1
    ext g
    simp [coreLin1, coreLin2]
    apply cf.ps1
  map_smul' := by
    intro x1 y1
    ext g
    simp [coreLin1, coreLin2]
    apply cf.pm1
}

-- Here we start lifting core to space of all triples.
-- Here we lift it from acting on c₁⊗c₂⊗c₃ to acting on c₁₂⊗c₃
noncomputable
def coreLift1(R: Type)[CommSemiring R][Ring R][Module R (Coup R)](cf: CF R):
    (doub R) →ₗ[R] (Coup R →ₗ[R] triple R) :=
TensorProduct.lift (coreLin3 R cf)

-- Final: Core lifted to c₁₂₃
noncomputable
def final(R: Type)[CommSemiring R][Ring R][Module R (Coup R)](cf: CF R):
    triple R →ₗ[R] triple R := TensorProduct.lift (coreLift1 R cf)
