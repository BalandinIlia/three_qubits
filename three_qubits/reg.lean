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

@[reducible]
def doub(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]:Type :=
    TensorProduct R (Coup R) (Coup R)
@[reducible]
def triple(R:Type)[CommSemiring R][Ring R][Module R (Coup R)]:Type :=
    TensorProduct R (doub R) (Coup R)

noncomputable
def pureDoub(R: Type)[CommSemiring R][Ring R][Module R (Coup R)](c1 c2: Coup R):doub R :=
    TensorProduct.tmul R c1 c2
noncomputable
def pureTriple(R: Type)[CommSemiring R][Ring R][Module R (Coup R)](c1 c2 c3: Coup R):triple R :=
    TensorProduct.tmul R (pureDoub R c1 c2) c3

lemma lemTr1(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
    (a b c d: Coup R): pureTriple R (a+b) c d = pureTriple R a c d + pureTriple R b c d := by
  simp [pureTriple]
  simp [pureDoub]
  rw [TensorProduct.add_tmul a b]
  rw [TensorProduct.add_tmul (a ⊗ₜ[R] c)]

lemma lemTr2(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
    (a b c d: Coup R): pureTriple R a (b+c) d = pureTriple R a b d + pureTriple R a c d := by
  simp [pureTriple]
  simp [pureDoub]
  rw [TensorProduct.tmul_add a b c]
  rw [TensorProduct.add_tmul (a ⊗ₜ[R] b)]

lemma lemTr3(R: Type)[CommSemiring R][Ring R][Module R (Coup R)]
    (a b c d: Coup R): pureTriple R a b (c+d) = pureTriple R a b c + pureTriple R a b d := by
  simp [pureTriple]
  simp [pureDoub]
  rw [TensorProduct.tmul_add]

#synth Module ℤ (triple ℤ)
