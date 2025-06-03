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

set_option maxHeartbeats 10000000

open TensorProduct

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

macro "extractSc":tactic =>
`(tactic|(
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul
))

-- Part 1: Coup definition, module over coup

-- A pair of integers
@[ext]
structure Coup where
f: ℤ
s: ℤ

-- prove tactic for module of pairs
macro "pr":tactic =>
`(tactic|(
  intros;
  simp [HAdd.hAdd, HSMul.hSMul, OfNat.ofNat];
  try all_goals simp [Zero.zero, Add.add, SMul.smul, HMul.hMul];
  try ext;
  try apply And.intro;
  all_goals simp [instAddNat, instMulNat, Int.instAdd, Int.instMul, OfNat.ofNat];
  all_goals ring
))

@[instance]
instance mon: AddCommMonoid Coup :=
{
  add(c1 c2: Coup):Coup := Coup.mk (c1.f+c2.f) (c1.s+c2.s)
  zero := Coup.mk 0 0
  add_assoc := by pr
  zero_add := by pr
  add_zero := by pr
  add_comm := by pr

  nsmul(n: ℕ)(c:Coup) := Coup.mk ((n:ℤ)*c.f) ((n:ℤ)*c.s)
  nsmul_zero := by pr
  nsmul_succ := by pr
}

@[instance]
instance g: HMul ℤ Coup Coup :=
{
  hMul(z:ℤ)(c:Coup):Coup := Coup.mk (z*c.f) (z*c.s)
}

@[instance]
instance mod: Module ℤ Coup :=
{
  smul(z:ℤ)(c: Coup) := z*c
  one_smul := by pr
  mul_smul := by
    simp [HSMul.hSMul]
    simp [HMul.hMul]
    simp [Mul.mul]
    intros
    apply And.intro
    all_goals ring
  smul_zero := by pr
  smul_add := by pr
  add_smul := by pr
  zero_smul := by pr
}

-- Part 2: triple and core function

-- Here we start the purpose of this file
-- triple is a "Tensor cube" of Coup
@[reducible]
def doub:Type := Coup ⊗[ℤ] Coup
@[reducible]
def triple:Type := doub ⊗[ℤ] Coup

noncomputable
def pureDoub(c1 c2: Coup):doub := TensorProduct.tmul ℤ c1 c2
noncomputable
def pureTriple(c1 c2 c3: Coup):triple := TensorProduct.tmul ℤ (pureDoub c1 c2) c3

#check TensorProduct.add_smul
#check TensorProduct.add_tmul
#check TensorProduct.tmul_add
lemma lemTr1(a b c d: Coup): pureTriple (a+b) c d = pureTriple a c d + pureTriple b c d := by
  simp [pureTriple]
  simp [pureDoub]
  rw [TensorProduct.add_tmul a b]
  rw [TensorProduct.add_tmul (a ⊗ₜ[ℤ] c)]

lemma lemTr2(a b c d: Coup): pureTriple a (b+c) d = pureTriple a b d + pureTriple a c d := by
  simp [pureTriple]
  simp [pureDoub]
  rw [TensorProduct.tmul_add a b c]
  rw [TensorProduct.add_tmul (a ⊗ₜ[ℤ] b)]

lemma lemTr3(a b c d: Coup): pureTriple a b (c+d) = pureTriple a b c + pureTriple a b d := by
  simp [pureTriple]
  simp [pureDoub]
  rw [TensorProduct.tmul_add]

-- FUNCTION PURPOSE
-- This function is a core of the transformation.
-- In fact this function defines transformation of triple instances.
-- However it defines it explicitly only for pure states: c₁⊗c₂⊗c₃.
-- This funcition is later lifted to define transformation for entangled states.
-- CF means core function
structure CF where
func: Coup → Coup → Coup → triple
ps1: ∀a b c d: Coup, func (a+b) c d = (func a c d) + (func b c d)
ps2: ∀a b c d: Coup, func a (b+c) d = (func a b d) + (func a c d)
ps3: ∀a b c d: Coup, func a b (c+d) = (func a b c) + (func a b d)
pm1: ∀m:ℤ, ∀a b c: Coup, func (m • a) b c = m • (func a b c)
pm2: ∀m:ℤ, ∀a b c: Coup, func a (m • b) c = m • (func a b c)
pm3: ∀m:ℤ, ∀a b c: Coup, func a b (m • c) = m • (func a b c)

-- Part 3: constructing core function

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

def sel(x y z: Coup)(n:ℕ):Coup :=
if n=1 then x else
if n=2 then y else
if n=3 then z else
0

noncomputable
def repl1(x y z: Coup)(p:ℕ):
         Coup →ₗ[ℤ] triple :=
{
  toFun(c:Coup) :=
    if p=1 then pureTriple c y z else
    if p=2 then pureTriple x c z else
    if p=3 then pureTriple x y c else
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
def repl2(x y z: Coup)(p1 p2:ℕ)(neq: ¬(p1=p2)):
        Coup →ₗ[ℤ] (Coup →ₗ[ℤ] triple) :=
{
  toFun(c:Coup) :=
    if p1=1 then repl1 c y z p2 else
    if p1=2 then repl1 x c z p2 else
    if p1=3 then repl1 x y c p2 else
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
        rw [lemTr1 a b c z]
      }
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr1 a b y c]
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
        rw [lemTr2 c a b z]
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
        rw [lemTr2 x a b c]
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
        rw [lemTr3 c y a b]
      }
      {
        intro eq2
        simp [eq2]
        ext c
        simp
        rw [lemTr3 x c a b]
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
def repl(x y z: Coup)(p1 p2:ℕ)(neq: ¬(p1=p2)):doub →ₗ[ℤ] triple := TensorProduct.lift (repl2 x y z p1 p2 neq)

structure CF2 where
func: Coup → Coup → doub
ps1: ∀a b c: Coup, func (a+b) c = (func a c) + (func b c)
ps2: ∀a b c: Coup, func a (b+c) = (func a b) + (func a c)
pm1: ∀m:ℤ, ∀a b: Coup, func (m • a) b = m • (func a b)
pm2: ∀m:ℤ, ∀a b: Coup, func a (m • b) = m • (func a b)

#check TensorProduct.add_smul
#check TensorProduct.add_tmul
#check TensorProduct.tmul_add
#check TensorProduct.smul_tmul
#check TensorProduct.smul_tmul'
noncomputable
def swappp:CF2 :=
{
  func := fun x y:Coup => pureDoub y x
  ps1:= by
    simp [pureDoub]
    intro a b c
    rw [TensorProduct.tmul_add c a b]
  ps2:= by
    simp [pureDoub]
    intro a b c
    rw [TensorProduct.add_tmul]
  pm1:= by
    simp [pureDoub]
  pm2:= by
    simp [pureDoub]
    intro m a b
    rw [TensorProduct.smul_tmul']
}

lemma distr(p: doub)(m1 m2 m3: doub →ₗ[ℤ] triple)
           (l: ∀a b: Coup, m1 (TensorProduct.tmul ℤ a b)=
                           m2 (TensorProduct.tmul ℤ a b)+
                           m3 (TensorProduct.tmul ℤ a b)):
  m1 p = m2 p + m3 p := by
  apply TensorProduct.induction_on (motive := fun g:doub => m1 g = m2 g + m3 g)
  aesop
  apply l
  intros x y a1 a2
  simp [a1, a2]
  module

lemma distr2(p: doub)(m1 m2: doub →ₗ[ℤ] triple)
            (l: ∀a b: Coup, m1 (TensorProduct.tmul ℤ a b)=
                           m2 (TensorProduct.tmul ℤ a b)):
  m1 p = m2 p := by
  apply TensorProduct.induction_on (motive := fun g:doub => m1 g = m2 g)
  aesop
  apply l
  intros x y a1 a2
  simp [a1, a2]

noncomputable
def transTwo(cf2: CF2)(p1 p2:ℕ)(neq: ¬(p1=p2)):CF :=
{
  func := fun x y z:Coup => repl x y z p1 p2 neq (cf2.func (sel x y z p1) (sel x y z p2))
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
        have eq:∀t y :Coup,
        (repl (a + b) c d 2 3 (by aesop))
          (TensorProduct.tmul ℤ t y) =
        (repl a c d 2 3 (by aesop))
          (TensorProduct.tmul ℤ t y) +
        (repl b c d 2 3 (by aesop))
          (TensorProduct.tmul ℤ t y) := by
          simp [repl]
          simp [repl2]
          simp [repl1]
          simp [lemTr1]
        apply distr (cf2.func c d)
        apply eq
      }
      intro e3 e4
      intro a b c d
      simp [e3, e4]
      generalize rt:(cf2.func c 0)=gh
      clear rt
      apply distr gh
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
        apply distr (cf2.func d c)
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
      apply distr (cf2.func d 0)
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
      apply distr (cf2.func 0 c)
      simp [repl, repl2, e1, e2, e3]
    }
    {
      intro c1
      simp [c1]
      intro a b c d
      apply distr (cf2.func 0 d)
      simp [repl, repl2, e1, e2, e3]
    }
    intro c1 c2 c3
    simp [c1, c2, c3]
    intro a b c d
    apply distr (cf2.func 0 0)
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
        have eq1:(repl a (b + c) d 1 2 (by aesop)) (cf2.func a b) =
                 (repl a b d 1 2 (by aesop)) (cf2.func a b):= by
          apply distr2 (cf2.func a b)
          simp [repl, repl2, repl1]
        have eq2:(repl a (b + c) d 1 2 (by aesop)) (cf2.func a c) =
                 (repl a c d 1 2 (by aesop)) (cf2.func a c):= by
          apply distr2 (cf2.func a c)
          simp [repl, repl2, repl1]
        simp [eq1, eq2]
      }
      {
        intro a b c d
        apply distr (cf2.func a d)
        simp [repl, repl2, repl1, lemTr2]
      }
      intro e3 e4
      simp [e3, e4]
      intro a b c d
      apply distr (cf2.func a 0)
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
        have eq1:(repl a (b + c) d 2 3 (by aesop)) (cf2.func b d) =
                 (repl a b d 2 3 (by aesop)) (cf2.func b d):= by
          apply distr2 (cf2.func b d)
          simp [repl, repl2, repl1]
        have eq2:(repl a (b + c) d 2 3 (by aesop)) (cf2.func c d) =
                 (repl a c d 2 3 (by aesop)) (cf2.func c d):= by
          apply distr2 (cf2.func c d)
          simp [repl, repl2, repl1]
        simp [eq1, eq2]
      }
      intro e3 e4
      intro a b c d
      simp [e3, e4]
      simp [cf2.ps1, cf2.ps2]
      have eq1:(repl a (b + c) d 2 p2 (by aesop)) (cf2.func b 0) =
               (repl a b d 2 p2 (by aesop)) (cf2.func b 0):= by
        apply distr2 (cf2.func b 0)
        simp [repl, repl2, repl1]
      have eq2:(repl a (b + c) d 2 p2 (by aesop)) (cf2.func c 0) =
               (repl a c d 2 p2 (by aesop)) (cf2.func c 0):= by
        apply distr2 (cf2.func c 0)
        simp [repl, repl2, repl1]
      simp [eq1, eq2]
    }
    all_goals sorry
  ps3:= by sorry
  pm1:= by sorry
  pm2:= by sorry
  pm3:= by sorry
}

noncomputable
def swa(p1 p2:ℕ)(neq: ¬(p1=p2)):=transTwo swappp p1 p2 neq

-- Here we start transforming core into linear map to linear map...
-- This is the first step: we eliminate the first parameter of core
noncomputable
def coreLin1(cf: CF)
            (x y: Coup):
            Coup →ₗ[ℤ] triple :=
{
  toFun(z:Coup) := cf.func x y z
  map_add' := by
    intro a b
    apply cf.ps3
  map_smul' := by
    intro m a
    apply cf.pm3
}

-- Here we continue transforming core into linea map.
-- Here we eliminate the second parameter of core.
noncomputable
def coreLin2(cf: CF)
            (x: Coup):
            Coup →ₗ[ℤ] (Coup →ₗ[ℤ] triple) :=
{
  toFun(y:Coup) := coreLin1 cf x y
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
def coreLin3(cf: CF):
            Coup →ₗ[ℤ] (
                      Coup →ₗ[ℤ] (
                                 Coup →ₗ[ℤ] triple
                                 )
                      ) :=
{
  toFun(c:Coup) := coreLin2 cf c
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
def coreLift1(cf: CF): (Coup ⊗[ℤ] Coup) →ₗ[ℤ] (Coup →ₗ[ℤ] triple) :=
TensorProduct.lift (coreLin3 cf)

-- Final: Core lifted to c₁₂₃
noncomputable
def final(cf: CF): triple →ₗ[ℤ] triple := TensorProduct.lift (coreLift1 cf)

-- Part 3: defining particular example terms

-- HOW THIS PARTICULAR INSTANCE WORKS
-- This particular instance takes the following parameters:
-- n: number of element unit transformation should be applied to (c₁ or c₂ or c₃)
-- tr: unit transformation
-- x: first element
-- y: second element
-- z: third element
noncomputable
def core(n: ℕ)
        (tr: Coup →ₗ[ℤ] Coup)
        (x: Coup)
        (y: Coup)
        (z:Coup):
        triple :=
if (n=1) then TensorProduct.tmul ℤ
                                 (TensorProduct.tmul ℤ (tr x) y)
                                 z
else if (n=2) then TensorProduct.tmul ℤ
                                      (TensorProduct.tmul ℤ x (tr y))
                                      z
else if (n=3) then TensorProduct.tmul ℤ
                                      (TensorProduct.tmul ℤ x y)
                                      (tr z)
else TensorProduct.tmul ℤ
                        (TensorProduct.tmul ℤ x y)
                        z



noncomputable
def coreFunc(n: ℕ)(tr: Coup →ₗ[ℤ] Coup): CF :=
{
  func := core n tr
  ps1 := by
    simp [core]
    intros
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  ps2 := by
    simp [core]
    intros
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  ps3 := by
    simp [core]
    intros
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  pm1 := by
    simp [core]
    intros
    apply help n
    all_goals aesop
  pm2 := by
    simp [core]
    intros
    apply help n
    all_goals aesop
  pm3 := by
    simp [core]
}

-- Here we are having an example to make sure the abovementioned functionality works as expected

-- transformation
def swap: Coup →ₗ[ℤ] Coup :=
{
  toFun(c:Coup) := Coup.mk c.s c.f
  map_add' := by pr
  map_smul' := by pr
}

-- triple examples
noncomputable
def ex1:triple := TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 3 4)) (Coup.mk 5 6)
noncomputable
def ex2:triple := TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 10 20) (Coup.mk 30 40)) (Coup.mk 50 60)

--Part 4: tests

-- first test theorem to make sure that final works as expected
theorem test1:final (coreFunc 1 swap) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 2 1) (Coup.mk 3 4)) (Coup.mk 5 6) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap]
  simp [core]

theorem testt:final (swa 1 3 (by aesop)) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 5 6) (Coup.mk 3 4)) (Coup.mk 1 2) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [swa, swappp, transTwo, repl, repl2, sel, pureDoub, repl1, pureTriple]

theorem testtt:final (swa 1 3 (by aesop)) (ex1+ex2) = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 5 6) (Coup.mk 3 4)) (Coup.mk 1 2)
      + TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 50 60) (Coup.mk 30 40)) (Coup.mk 10 20)
  := by
  simp [ex1, ex2]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [swa, swappp, transTwo, repl, repl2, sel, pureDoub, repl1, pureTriple]

theorem test2:final (coreFunc 2 swap) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 4 3)) (Coup.mk 5 6) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap]
  simp [core]

theorem test3:final (coreFunc 2 swap) (ex1+ex2) =
            TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 4 3)) (Coup.mk 5 6) +
            TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 10 20) (Coup.mk 40 30)) (Coup.mk 50 60) := by
  have eq: final (coreFunc 2 swap) (ex1+ex2) = (final (coreFunc 2 swap) ex1) + (final (coreFunc 2 swap) ex2) := by
    simp [final]
  rw [eq]
  clear eq

  simp [ex1, ex2]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap]
  simp [core]


theorem test4:final (coreFunc 3 swap) ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 3 4)) (Coup.mk 6 5) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [coreFunc]
  simp [swap]
  simp [core]
